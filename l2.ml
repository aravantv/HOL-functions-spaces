(* ========================================================================= *)
(*                                                                           *)
(*                Library of complex function vector spaces:                 *)
(*                  Application to complex vectors.                          *)
(*                                                                           *)
(*             (c) Copyright, Vincent Aravantinos, 2013                      *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*                 Contact: <vincent@ece.concordia.ca>                       *)
(*                                                                           *)
(* ========================================================================= *)


g `is_cfun_subspace { f | f integrable_on (:real)}`
INTEGRABLE_ADD
INTEGRABLE_CMUL

g `is_inner_space ({ f | f integrable_on (:real)}, \f g. integral (:real) (\x. f x * g x))`
