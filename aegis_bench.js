var aegisBench = (function(){
  function benchEncrypt() {
    let key = new Uint8Array([0x10,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00]);
    let nonce = new Uint8Array([0x10,0x00,0x02,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00]);
    let data = new Uint8Array([]);
    let msg = new Uint8Array(102400);
    n = 1000;

    performance.mark("start");
    for (let i = 0; i < n; i++) {
      aegis128L.seal(key, nonce, msg, data, false);
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

    const tag = aegis128L.seal(key, nonce, msg, data);
    let ciphertext = msg.slice();

    performance.mark("start");
    for (let i = 0; i < n; i++) {
      aegis128L.open(key, nonce, ciphertext, data, tag);
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

  return benchmarks
})();
