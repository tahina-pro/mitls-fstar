(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
(** Expansion of secrets into expanded secrets *)
module KDF.Salt.ODH

open TLSMem
open TLSMem
open TLSMem

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSInfo

module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = TLSMem
module HS = TLSMem

(* Source index is a secret index *)
type id = secretId

type state (i:id) =
  | State: r:rgn -> state i
