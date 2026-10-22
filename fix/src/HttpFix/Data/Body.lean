/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import HttpFix.Data.Body.Basic
public import HttpFix.Data.Body.Length
public import HttpFix.Data.Body.Any
public import HttpFix.Data.Body.Stream
public import HttpFix.Data.Body.Empty
public import HttpFix.Data.Body.Full
public import HttpFix.Data.Body.Replayable

public section

/-!
# Body

This module re-exports all HTTP body types: `Body.Empty`, `Body.Full`, `Body.Stream`,
`Body.Any`, and `Body.Length`, along with the `Http.Body` typeclass and conversion
utilities (`ToByteArray`, `FromByteArray`).
-/
