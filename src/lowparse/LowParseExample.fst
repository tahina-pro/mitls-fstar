module LowParseExample

let f (input: FStar.Bytes.bytes) : Tot (LowParse.SLow.result (LowParseExample.Aux.t * FStar.UInt32.t)) =
  LowParseExample.Aux.parse32_t input

let g (input: FStar.Bytes.bytes) : Tot (LowParse.SLow.result (LowParse.SLow.array LowParseExample.Aux.t 18 * FStar.UInt32.t)) =
  LowParseExample.Aux.parse32_t_array input

let j (input: FStar.Bytes.bytes) : Tot (LowParse.SLow.result (LowParse.SLow.vlarray LowParseExample.Aux.t 5 7 * FStar.UInt32.t)) =
  LowParseExample.Aux.parse32_t_vlarray input

let m (x: LowParseExample.Aux.t) : Tot FStar.Bytes.bytes =
  LowParseExample.Aux.serialize32_t x

let s (x: LowParse.SLow.array LowParseExample.Aux.t 18) : Tot FStar.Bytes.bytes =
  LowParseExample.Aux.serialize32_t_array x

let main () : Tot FStar.Int32.t = 0l
