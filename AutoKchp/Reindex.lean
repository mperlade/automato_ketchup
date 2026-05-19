/-
Copyright (c) 2026 Marc Perlade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Perlade
-/

module

public import AutoKchp.CDFA

public section

structure ReindexResult {a: Nat} (r: CDFA a) where
  reindexed: NatCDFA a
  correct: reindexed.accepts = r.accepts

end
