/* EMLE data vault worker: fetch → decrypt → gunzip → JSON.parse (off main thread) */

function _secVaultDecrypt(cipherBytes) {
  const _k = [69, 77, 76, 69, 95, 83, 69, 67, 85, 82, 69, 95, 86, 65, 85, 76, 84, 95, 50, 48, 50, 54, 95, 64, 104, 109, 51, 100, 95, 65, 109, 51, 114, 95, 78, 117, 116, 115, 104, 101, 108, 108, 95, 35, 75, 101, 121, 57, 57]
    .map((c) => String.fromCharCode(c))
    .join("");
  const S = new Uint8Array(256);
  for (let i = 0; i < 256; i++) S[i] = i;
  let j = 0;
  for (let i = 0; i < 256; i++) {
    j = (j + S[i] + _k.charCodeAt(i % _k.length)) % 256;
    const tmp = S[i];
    S[i] = S[j];
    S[j] = tmp;
  }
  let i = 0;
  j = 0;
  const out = new Uint8Array(cipherBytes.length);
  for (let k = 0; k < cipherBytes.length; k++) {
    i = (i + 1) % 256;
    j = (j + S[i]) % 256;
    const tmp = S[i];
    S[i] = S[j];
    S[j] = tmp;
    out[k] = cipherBytes[k] ^ S[(S[i] + S[j]) % 256];
  }
  return out;
}

function _pureJsGunzip(buf) {
  let pos = 0;
  if (buf[0] === 0x1f && buf[1] === 0x8b) {
    const flg = buf[3];
    pos = 10;
    if (flg & 4) {
      const xlen = buf[pos] | (buf[pos + 1] << 8);
      pos += 2 + xlen;
    }
    if (flg & 8) {
      while (buf[pos++] !== 0) {}
    }
    if (flg & 16) {
      while (buf[pos++] !== 0) {}
    }
    if (flg & 2) pos += 2;
  }

  const end = buf[0] === 0x1f && buf[1] === 0x8b ? buf.length - 8 : buf.length;
  let bitPos = pos * 8;

  const readBits = (n) => {
    let val = 0;
    for (let i = 0; i < n; i++) {
      val |= ((buf[bitPos >> 3] >> (bitPos & 7)) & 1) << i;
      bitPos++;
    }
    return val;
  };

  const buildTree = (lengths) => {
    let maxBits = 0;
    for (let i = 0; i < lengths.length; i++) if (lengths[i] > maxBits) maxBits = lengths[i];
    const blCount = new Uint16Array(maxBits + 1);
    for (let i = 0; i < lengths.length; i++) if (lengths[i]) blCount[lengths[i]]++;
    const nextCode = new Uint16Array(maxBits + 1);
    let code = 0;
    for (let bits = 1; bits <= maxBits; bits++) {
      code = (code + blCount[bits - 1]) << 1;
      nextCode[bits] = code;
    }
    const map = {};
    for (let n = 0; n < lengths.length; n++) {
      const len = lengths[n];
      if (len !== 0) {
        map[(len << 16) | nextCode[len]] = n;
        nextCode[len]++;
      }
    }
    return { map, maxBits };
  };

  const decodeSym = (tree) => {
    let code = 0;
    for (let len = 1; len <= tree.maxBits; len++) {
      code = (code << 1) | ((buf[bitPos >> 3] >> (bitPos & 7)) & 1);
      bitPos++;
      const sym = tree.map[(len << 16) | code];
      if (sym !== undefined) return sym;
    }
    throw new Error("Invalid Huffman code");
  };

  const fixedLit = (() => {
    const l = new Uint8Array(288);
    for (let i = 0; i <= 143; i++) l[i] = 8;
    for (let i = 144; i <= 255; i++) l[i] = 9;
    for (let i = 256; i <= 279; i++) l[i] = 7;
    for (let i = 280; i <= 287; i++) l[i] = 8;
    return buildTree(l);
  })();

  const fixedDist = buildTree(new Uint8Array(32).fill(5));
  const lenBase = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
  const lenExtra = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
  const distBase = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
  const distExtra = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
  const clOrder = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

  let out = new Uint8Array(buf.length * 4);
  let outPos = 0;

  const ensureCap = (add) => {
    if (outPos + add <= out.length) return;
    const next = new Uint8Array(Math.max(out.length * 2, outPos + add + 65536));
    next.set(out.subarray(0, outPos));
    out = next;
  };

  let bfinal = 0;
  while (!bfinal && bitPos >> 3 < end) {
    bfinal = readBits(1);
    const btype = readBits(2);
    if (btype === 0) {
      bitPos = (bitPos + 7) & ~7;
      const p = bitPos >> 3;
      const len = buf[p] | (buf[p + 1] << 8);
      bitPos += 32;
      ensureCap(len);
      out.set(buf.subarray(p + 4, p + 4 + len), outPos);
      outPos += len;
      bitPos += len * 8;
    } else if (btype === 1 || btype === 2) {
      let litTree = fixedLit;
      let distTree = fixedDist;
      if (btype === 2) {
        const hlit = readBits(5) + 257;
        const hdist = readBits(5) + 1;
        const hclen = readBits(4) + 4;
        const clLens = new Uint8Array(19);
        for (let i = 0; i < hclen; i++) clLens[clOrder[i]] = readBits(3);
        const clTree = buildTree(clLens);
        const lens = new Uint8Array(hlit + hdist);
        let idx = 0;
        while (idx < hlit + hdist) {
          const sym = decodeSym(clTree);
          if (sym < 16) lens[idx++] = sym;
          else {
            let rep = 0;
            let val = 0;
            if (sym === 16) {
              val = lens[idx - 1];
              rep = 3 + readBits(2);
            } else if (sym === 17) {
              val = 0;
              rep = 3 + readBits(3);
            } else {
              val = 0;
              rep = 11 + readBits(7);
            }
            while (rep--) lens[idx++] = val;
          }
        }
        litTree = buildTree(lens.subarray(0, hlit));
        distTree = buildTree(lens.subarray(hlit));
      }
      while (true) {
        const sym = decodeSym(litTree);
        if (sym === 256) break;
        if (sym < 256) {
          ensureCap(1);
          out[outPos++] = sym;
        } else {
          const lIdx = sym - 257;
          const length = lenBase[lIdx] + readBits(lenExtra[lIdx]);
          const dIdx = decodeSym(distTree);
          const dist = distBase[dIdx] + readBits(distExtra[dIdx]);
          ensureCap(length);
          for (let i = 0; i < length; i++) {
            out[outPos] = out[outPos - dist];
            outPos++;
          }
        }
      }
    } else {
      throw new Error("Invalid DEFLATE block type");
    }
  }

  return out.subarray(0, outPos);
}

async function _gunzipBytesSafe(bytes) {
  if (typeof DecompressionStream !== "undefined") {
    try {
      const ds = new DecompressionStream("gzip");
      const readerPromise = new Response(ds.readable).arrayBuffer();
      const writer = ds.writable.getWriter();
      const CHUNK = 65536;
      for (let off = 0; off < bytes.length; off += CHUNK) {
        await writer.write(bytes.subarray(off, off + CHUNK));
      }
      await writer.close();
      const buf = await readerPromise;
      return new TextDecoder("utf-8").decode(buf);
    } catch (e) {
      console.warn("DecompressionStream fallback triggered:", e);
    }
  }
  const plain = _pureJsGunzip(bytes);
  return new TextDecoder("utf-8").decode(plain);
}

function fingerprintPayload(b64) {
  const size = b64.length;
  const first64 = b64.slice(0, 64);
  const last64 = b64.slice(-64);
  return size + "|" + first64 + "|" + last64;
}

function progress(stage) {
  self.postMessage({ type: "progress", stage });
}

async function loadVault(cachedFingerprint) {
  progress("fetch");
  const res = await fetch("./data.enc?v=20261124-ai-label1", { cache: "no-cache" });
  if (!res.ok) {
    throw new Error("Failed to fetch data.enc (" + res.status + ")");
  }
  const b64 = (await res.text()).trim();
  if (!b64) throw new Error("Empty data.enc payload");

  const fingerprint = fingerprintPayload(b64);
  if (cachedFingerprint && cachedFingerprint === fingerprint) {
    self.postMessage({ type: "cache-hit", fingerprint });
    return;
  }

  progress("decrypt");
  const binStr = atob(b64);
  const rawBytes = new Uint8Array(binStr.length);
  for (let i = 0; i < binStr.length; i++) rawBytes[i] = binStr.charCodeAt(i);
  const bytes = _secVaultDecrypt(rawBytes);

  progress("inflate");
  const text = await _gunzipBytesSafe(bytes);

  progress("parse");
  const data = JSON.parse(text);
  self.postMessage({ type: "ready", data, fingerprint });
}

self.onmessage = (e) => {
  const msg = e.data || {};
  if (msg.type !== "load") return;
  loadVault(msg.cachedFingerprint || null).catch((err) => {
    self.postMessage({
      type: "error",
      message: (err && err.message) || "Data load failed",
    });
  });
};
