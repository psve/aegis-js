var aegis128L = (function(){
  /*************************/
  /*** Utility functions ***/
  /*************************/

  function hex2arr(hex) {
    let bytes = [];
    for (let c = 0; c < hex.length; c += 2) {
      bytes.push(parseInt(hex.substr(c, 2), 16));
    }
    return bytes;
  }

  function arr2hex(a) {
    return a.reduce(function(p, c){ return p + c.toString(16).padStart(2, '0') }, '');
  }

  function logState(s) {
    let out = "";
    for (let i = 0 ; i < 8 ; i++) {
      let x = new Uint8Array(s[i].buffer);
      out += arr2hex(x) + "\n";
    }
    console.log(out);
  }

  function logTag(t) {
    let x = new Uint8Array(t.buffer);
    console.log(arr2hex(x));
  }

  /*************************/
  /*** Private functions ***/
  /*************************/

  const keyBytes = 16;
  const nonceBytes = 16;
  const tagBytes = 16;
  const const0 = new Uint32Array([0x02010100, 0xd080503, 0x59372215, 0x6279e990]);
  const const1 = new Uint32Array([0x55183ddb, 0xf12fc26d, 0x42311120, 0xdd28b573]);
  let t = [[],[],[],[]];
  let s32 = undefined;
  let s8 = undefined;

  function init() {
    if (!t[0][0]) {
      var x, xInv, d=[], th=[], x2, s, tEnc;

      // Compute double and third tables
      for (let i = 0; i < 256; i++) {
        th[( d[i] = i<<1 ^ (i>>7)*283 )^i]=i;
      }

      x = xInv = 0;

      for (let j = 0 ; j < 256; j++) {
        s = xInv ^ xInv<<1 ^ xInv<<2 ^ xInv<<3 ^ xInv<<4;
        s = s>>8 ^ s&255 ^ 99;
        x2 = d[x];
        tEnc = d[s]*0x101 ^ s*0x1010100;

        for (let i = 0; i < 4; i++) {
          t[i][x] = tEnc = tEnc<<24 ^ tEnc>>>8;
        }

        x ^= x2 || 1
        xInv = th[xInv] || 1
      }

      // Swap byte order
      for (let i = 0; i < 4; i++) {
        for (let j = 0; j < 256; j++) {
          t[i][j] = ((t[i][j] << 24) & 0xff000000) ^ ((t[i][j] << 8) & 0x00ff0000) ^ ((t[i][j] >> 8) & 0x0000ff00) ^ ((t[i][j] >> 24) & 0x000000ff);
        }
      }
    }
  }

  // AES round function implementation inspired by
  // https://github.com/bitwiseshiftleft/sjcl
  function round(src8, key32, dst32) {
    const x0 = t[0][src8[0]]  ^ t[1][src8[5]]  ^ t[2][src8[10]] ^ t[3][src8[15]];
    const x1 = t[0][src8[4]]  ^ t[1][src8[9]]  ^ t[2][src8[14]] ^ t[3][src8[3]];
    const x2 = t[0][src8[8]]  ^ t[1][src8[13]] ^ t[2][src8[2]]  ^ t[3][src8[7]];
    const x3 = t[0][src8[12]] ^ t[1][src8[1]]  ^ t[2][src8[6]]  ^ t[3][src8[11]];

    dst32[0] = key32[0] ^ x0;
    dst32[1] = key32[1] ^ x1;
    dst32[2] = key32[2] ^ x2;
    dst32[3] = key32[3] ^ x3;
  }

  function tagValid(a, b) {
    let equal = true;
    for (let i = 0 ; i < a.byteLength ; i++) {
      equal &= (a[i] == b[i]);
    }
    return equal;
  }

  function zeroPad(data, withTag) {
    if (data.byteLength%32 != 0) {
      let padLen = 32 - data.byteLength%32;
      let padded = new Uint8Array(data.byteLength + padLen);
      padded.set(data);
      return new Uint32Array(padded.buffer);
    }
    return new Uint32Array(data.buffer);
  }

  function extract(a, b, c, d) {
    return [
      (a[0]&b[0]) ^ c[0] ^ d[0],
      (a[1]&b[1]) ^ c[1] ^ d[1],
      (a[2]&b[2]) ^ c[2] ^ d[2],
      (a[3]&b[3]) ^ c[3] ^ d[3],
    ];
  }

  function xor128into(val, dst, dstOffset) {
    dst[dstOffset + 0] ^= val[0];
    dst[dstOffset + 1] ^= val[1];
    dst[dstOffset + 2] ^= val[2];
    dst[dstOffset + 3] ^= val[3];
  }

  function update(a, aOffset, b, bOffset) {
    let t = s8[7].slice();

    round(s8[6], s32[7], s32[7]);
    round(s8[5], s32[6], s32[6]);
    round(s8[4], s32[5], s32[5]);

    s32[4][0] ^= b[bOffset+0];
    s32[4][1] ^= b[bOffset+1];
    s32[4][2] ^= b[bOffset+2];
    s32[4][3] ^= b[bOffset+3];

    round(s8[3], s32[4], s32[4]);
    round(s8[2], s32[3], s32[3]);
    round(s8[1], s32[2], s32[2]);
    round(s8[0], s32[1], s32[1]);

    s32[0][0] ^= a[aOffset+0];
    s32[0][1] ^= a[aOffset+1];
    s32[0][2] ^= a[aOffset+2];
    s32[0][3] ^= a[aOffset+3];

    round(t, s32[0], s32[0]);
  }

  // Inputs are all Uint8Array.
  function process(key, nonce, msg, data, decrypt) {
    if (key.byteLength != keyBytes) {
      throw new Error("invalid key size");
    }
    if (nonce.byteLength != nonceBytes) {
      throw new Error("invalid nonce size");
    }

    init();

    const msgLen = msg.byteLength;
    const dataLen = data.byteLength;

    const keyArray = new Uint32Array(key.buffer);
    const nonceArray = new Uint32Array(nonce.buffer);
    const msgArray = zeroPad(msg);
    const dataArray = zeroPad(data);

    // Initialize
    s32 = [
      new Uint32Array(keyArray),
      new Uint32Array(const1),
      new Uint32Array(const0),
      new Uint32Array(const1),
      new Uint32Array(keyArray),
      new Uint32Array(keyArray),
      new Uint32Array(keyArray),
      new Uint32Array(keyArray),
    ];
    s8 = [
      new Uint8Array(s32[0].buffer),
      new Uint8Array(s32[1].buffer),
      new Uint8Array(s32[2].buffer),
      new Uint8Array(s32[3].buffer),
      new Uint8Array(s32[4].buffer),
      new Uint8Array(s32[5].buffer),
      new Uint8Array(s32[6].buffer),
      new Uint8Array(s32[7].buffer),
    ]

    xor128into(nonceArray, s32[0], 0);
    xor128into(nonceArray, s32[4], 0);
    xor128into(const0, s32[5], 0);
    xor128into(const1, s32[6], 0);
    xor128into(const0, s32[7], 0);

    for (let i = 0 ; i < 10 ; i++) {
      update(nonceArray, 0, keyArray, 0)
    }

    // Process associated data
    const dataBlocks = dataArray.byteLength/32;
    for (let i = 0 ; i < dataBlocks ; i++) {
      update(dataArray, i*8, dataArray, i*8+4)
    }

    // Process plaintext
    const msgBlocks = msgArray.byteLength/32;
    for (let i = 0 ; i < msgBlocks ; i++) {
      const z0 = extract(s32[2], s32[3], s32[1], s32[6]);
      const z1 = extract(s32[6], s32[7], s32[5], s32[2]);

      if (!decrypt) {
        update(msgArray, i*8, msgArray, i*8+4);
      }

      xor128into(z0, msgArray, i*8);
      xor128into(z1, msgArray, i*8+4);

      if (decrypt) {
        // Recreate zero padding if needed
        if (msgLen < (i+1)*32) {
          let x = new Uint8Array(msgArray.buffer);
          x.fill(0, msgLen);
        }
        update(msgArray, i*8, msgArray, i*8+4);
      }
    }
    const x = new Uint8Array(msgArray.buffer);
    msg.set(x.slice(0, msgLen));

    // Generate tag
    const tag64 = new BigUint64Array([BigInt(dataLen)*8n, BigInt(msgLen)*8n]);
    let tag = new Uint32Array(tag64.buffer);
    xor128into(s32[2], tag, 0);
    for (let i = 0 ; i < 7 ; i++) {
      update(tag, 0, tag, 0);
    }
    tag = s32[0];
    xor128into(s32[1], tag, 0);
    xor128into(s32[2], tag, 0);
    xor128into(s32[3], tag, 0);
    xor128into(s32[4], tag, 0);
    xor128into(s32[5], tag, 0);
    xor128into(s32[6], tag, 0);
    return tag.buffer;
  }

  /************************/
  /*** Public functions ***/
  /************************/

  function seal(key, nonce, msg, data) {
    return process(key, nonce, msg, data, false);
  }

  function open(key, nonce, msg, data, tag) {
    const tagDecrypt = process(key, nonce, msg, data, true);
    if (!tagValid(tag, tagDecrypt)) {
      msg.fill(0);
      return false;
    }
    return true;
  }

  /*************/
  /*** Tests ***/
  /*************/

  function testSanity() {
    let key = new Uint8Array(hex2arr("000102030405060708090a0b0c0d0e0f"));
    let nonce = new Uint8Array(hex2arr("101112131415161718191a1b1c1d1e1f"));
    let data = new Uint8Array(hex2arr("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20212223242526272829"));
    let plaintext = new Uint8Array(hex2arr("101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f3031323334353637"));

    let msg = plaintext.slice();

    let tagEncrypt = seal(key, nonce, msg, data);
    if (arr2hex(msg) == arr2hex(plaintext)) {
      console.log("encryption failed");
    }

    let valid = open(key, nonce, msg, data, tagEncrypt);
    if (!valid) {
      console.log("tag verification failed");
    }
    if (arr2hex(msg) != arr2hex(plaintext)) {
      console.log("decryption failed");
    }
  }

  function testInvalidTag() {
    let key = new Uint8Array(hex2arr("000102030405060708090a0b0c0d0e0f"));
    let nonce = new Uint8Array(hex2arr("101112131415161718191a1b1c1d1e1f"));
    let data = new Uint8Array(hex2arr("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20212223242526272829"));
    let plaintext = new Uint8Array(hex2arr("101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f3031323334353637"));

    let msg = plaintext.slice();

    let tagEncrypt = seal(key, nonce, msg, data);
    tagEncrypt[0] ^= 1;

    let valid = open(key, nonce, msg, data, tagEncrypt);
    if (valid) {
      console.log("tag verification should have failed");
    }
    if (!msg.every(function(e) {return e == 0})) {
      console.log("message wasn't wiped");
    }
  }

  function testKnownAnswers() {
    const tests = [
      {
        key:   "10010000000000000000000000000000",
        nonce: "10000200000000000000000000000000",
        data:  "",
        msg:   "00000000000000000000000000000000",
        ct:    "c1c0e58bd913006feba00f4b3cc3594e",
        tag:   "abe0ece80c24868a226a35d16bdae37a",
      },
      {
        key:   "10010000000000000000000000000000",
        nonce: "10000200000000000000000000000000",
        data:  "",
        msg:   "",
        ct:    "",
        tag:   "c2b879a67def9d74e6c14f708bbcc9b4",
      },
      {
        key:   "10010000000000000000000000000000",
        nonce: "10000200000000000000000000000000",
        data:  "0001020304050607",
        msg:   "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
        ct:    "79d94593d8c2119d7e8fd9b8fc77845c5c077a05b2528b6ac54b563aed8efe84",
        tag:   "cc6f3372f6aa1bb82388d695c3962d9a",
      },
      {
        key:   "10010000000000000000000000000000",
        nonce: "10000200000000000000000000000000",
        data:  "0001020304050607",
        msg:   "000102030405060708090a0b0c0d",
        ct:    "79d94593d8c2119d7e8fd9b8fc77",
        tag:   "5c04b3dba849b2701effbe32c7f0fab7",
      },
      {
        key:   "10010000000000000000000000000000",
        nonce: "10000200000000000000000000000000",
        data:  "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20212223242526272829",
        msg:   "101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f3031323334353637",
        ct:    "b31052ad1cca4e291abcf2df3502e6bdb1bfd6db36798be3607b1f94d34478aa7ede7f7a990fec10",
        tag:   "7542a745733014f9474417b337399507",
      },
    ];

    let i = 0;
    for (const test of tests) {
      let key = new Uint8Array(hex2arr(test.key));
      let nonce = new Uint8Array(hex2arr(test.nonce));
      let data = new Uint8Array(hex2arr(test.data));
      let msg = new Uint8Array(hex2arr(test.msg));

      let tag = seal(key, nonce, msg, data);

      if (test.ct != arr2hex(msg)) {
        console.log("(", i, ") wrong ciphertext: ", test.ct, "!=", arr2hex(msg));
      }
      if (test.tag != arr2hex(new Uint8Array(tag))) {
        console.log("(", i, ") wrong tag: ", test.tag, "!=", arr2hex(new Uint8Array(tag)));
      }

      i++;
    }
  }

  function unitTest() {
    testSanity();
    testInvalidTag();
    testKnownAnswers();
  }

  /******************/
  /*** Benchmarks ***/
  /******************/

  function benchEncrypt() {
    let key = new Uint8Array([0x10,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00]);
    let nonce = new Uint8Array([0x10,0x00,0x02,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00]);
    let data = new Uint8Array([]);
    let msg = new Uint8Array(102400);
    n = 1000;

    performance.mark("start");
    for (let i = 0; i < n; i++) {
      seal(key, nonce, msg, data, false);
    }
    performance.mark("stop");
    d = performance.measure("", "start", "stop");

    console.log(`Aegis encrypt: Total time: ${d.duration} ms`)
    console.log(`Aegis encrypt: Time per op: ${d.duration/n} ms`)
    console.log(`Aegis encrypt: Bytes per second: ${(n*msg.byteLength)/(d.duration/1000)}`)
    console.log(`Aegis encrypt: Nanoseconds per byte: ${(d.duration*1000000)/(n*msg.byteLength)}`)
  }

  function benchDecrypt() {
    let key = new Uint8Array([0x10,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00]);
    let nonce = new Uint8Array([0x10,0x00,0x02,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00]);
    let data = new Uint8Array([]);
    let msg = new Uint8Array(102400);
    n = 1000;

    const tag = seal(key, nonce, msg, data);
    let ciphertext = msg.slice();

    performance.mark("start");
    for (let i = 0; i < n; i++) {
      open(key, nonce, ciphertext, data, tag);
    }
    performance.mark("stop");
    d = performance.measure("", "start", "stop");

    console.log(`Aegis decrypt: Total time: ${d.duration} ms`)
    console.log(`Aegis decrypt: Time per op: ${d.duration/n} ms`)
    console.log(`Aegis decrypt: Bytes per second: ${(n*msg.byteLength)/(d.duration/1000)}`)
    console.log(`Aegis decrypt: Nanoseconds per byte: ${(d.duration*1000000)/(n*msg.byteLength)}`)
  }

  function benchmarks() {
    benchEncrypt();
    benchDecrypt();
  }

  return {
    seal,
    open,
    unitTest,
    benchmarks
  }
})();
