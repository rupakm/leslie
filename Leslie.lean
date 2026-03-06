-- This module serves as the root of the `Leslie` library.
-- Import modules here that should be built as part of the library.

import «Leslie».Rules.Basic
import «Leslie».Rules.BigOp
import «Leslie».Rules.LeadsTo
import «Leslie».Rules.StatePred
import «Leslie».Rules.WF
import «Leslie».Tactics.Basic
import «Leslie».Tactics.Modality
import «Leslie».Tactics.Structural
import «Leslie».Tactics.StateFinite
import «Leslie».Refinement
import «Leslie».Action
import «Leslie».Examples.CounterRefinement
import «Leslie».Examples.TwoPhaseCommit
import «Leslie».Layers
import «Leslie».Examples.TicketLock
import «Leslie».Examples.Paxos
import «Leslie».Examples.KVStore
import «Leslie».Simulate
