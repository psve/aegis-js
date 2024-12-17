var aegisTest = (function(){
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

  /*************/
  /*** Tests ***/
  /*************/

  function testSanity() {
    let key = new Uint8Array(hex2arr("000102030405060708090a0b0c0d0e0f"));
    let nonce = new Uint8Array(hex2arr("101112131415161718191a1b1c1d1e1f"));
    let data = new Uint8Array(hex2arr("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20212223242526272829"));
    let plaintext = new Uint8Array(hex2arr("101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f3031323334353637"));

    let msg = plaintext.slice();

    let tagEncrypt = aegis128L.seal(key, nonce, msg, data);
    if (arr2hex(msg) == arr2hex(plaintext)) {
      console.log("encryption failed");
    }

    let valid = aegis128L.open(key, nonce, msg, data, tagEncrypt);
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

    let tagEncrypt = aegis128L.seal(key, nonce, msg, data);

    let tag_uint8 = new Uint8Array(tagEncrypt);
    tag_uint8[0] ^= 1;

    let valid = aegis128L.open(key, nonce, msg, data, tagEncrypt);
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

      let tag = aegis128L.seal(key, nonce, msg, data);

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

  return unitTest
})();
