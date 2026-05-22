# Leslie_LTS: Labelled Transition Systems in Lean 4

Leslie_LTS is a framework for specifying and verifying systems modelled as
Labelled Transition Systems (LTS). It supports simulation proofs, parallel
composition, adversarial models, probabilistic reasoning, and secrecy
properties — with a focus on Byzantine fault-tolerant protocols.

## Building

From the repository root:

```
make LTS
```

## Usage

```lean
import Leslie_LTS
```

## Framework Modules

| Module | Description |
|--------|-------------|
| `Basic` | Core `LTS.System` definition, reachability, reflexive-transitive closure |
| `Trace` | Infinite traces and trace properties |
| `LTL` | Linear temporal logic operators |
| `Rules` | Proof rules for safety and invariants |
| `Liveness` | Liveness properties, fairness, WF1, leads-to |
| `Simulation` | Forward/backward simulation relations |
| `Composition` | Parallel composition of systems |
| `Probabilistic` | Probabilistic transitions and reasoning |
| `ProbExec` | Probabilistic execution semantics |
| `Adversary` | Adversarial and corruption models |
| `Secrecy` | Information-flow and secrecy properties |

## Examples

| Example | Description |
|---------|-------------|
| `BrachaBRB` | Bracha's Byzantine Reliable Broadcast |
| `BRB_Simulation` | Simulation proof for Bracha BRB |
| `BCA` / `IdealBCA` | Byzantine Consistent Agreement and its ideal specification |
| `BCA_Simulation` | Simulation proof: BCA refines IdealBCA |
| `DoubleBCA` / `DoubleBCA2` | Double-instance BCA compositions |
| `DoubleBCA_Simulation` / `DoubleBCA2_Simulation` | Simulation proofs for composed BCA |
| `DoubleIdealBCA` / `DoubleIdealBCA2` | Ideal specifications for composed BCA |
| `IdealBRB` | Ideal BRB specification |
| `RabinICP` | Rabin's Information-Checking Protocol |
| `ARS` | Abstract Rewriting Systems |
| `CorruptionInvariants` | Invariants under adversarial corruption |
| `UtilityByzantine` | Shared Byzantine utility lemmas |
