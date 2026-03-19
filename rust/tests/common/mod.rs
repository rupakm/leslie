//! Shared test harness for running bounded protocol instances.
//!
//! Two simulators matching the two protocol styles in Leslie:
//!
//! - **Round-based** (`run_rounds`): Models N processes communicating
//!   synchronously per round, with heard-of (HO) sets controlling which
//!   messages are delivered. Used for consensus protocols like OneThirdRule.
//!
//! - **Action-based** (`run_actions`): Models a nondeterministic state
//!   machine where one action fires at a time. Used for asynchronous
//!   protocols like LeaseLock.
//!
//! Both simulators are single-threaded and pure — no network, no threads,
//! just function calls. They check invariants after every step.

#![allow(dead_code)]
use std::collections::BTreeMap;

// ── Round-based simulator ──────────────────────────────────────────

/// Simulate `n` processes running a round-based protocol.
///
/// Each round:
///   1. Every process produces a message via `send(id, &state)`.
///   2. Messages are delivered per the HO set: `ho(round, receiver, sender)`.
///   3. Every process updates via `update(id, &state, &inbox, oracle)`.
///   4. The `check` callback asserts invariants on the current states.
///
/// Returns the final states after `num_rounds` rounds.
///
/// # Example
///
/// ```ignore
/// // Run 3 processes for 10 rounds with reliable (all-to-all) delivery
/// let final_states = run_rounds(
///     3, 10,
///     |id| MyProtocol::new(id, 3),           // init
///     |id, s| s.send_msg(id),                 // send
///     |id, s, inbox, _| s.update_msg(inbox),  // update
///     ho_reliable,                             // HO: all messages delivered
///     |_, _| (),                               // oracle: deterministic
///     |round, states| { /* check invariants */ },
/// );
/// ```
pub fn run_rounds<S: Clone, M: Clone, O: Clone>(
    n: usize,
    num_rounds: usize,
    init: impl Fn(usize) -> S,
    send: impl Fn(usize, &S) -> M,
    update: impl Fn(usize, &S, &BTreeMap<usize, M>, O) -> S,
    ho: impl Fn(usize, usize, usize) -> bool,
    oracle: impl Fn(usize, usize) -> O,
    check: impl Fn(usize, &[S]),
) -> Vec<S> {
    let mut states: Vec<S> = (0..n).map(&init).collect();
    check(0, &states);

    for round in 0..num_rounds {
        // 1. All processes send
        let messages: Vec<M> = (0..n).map(|i| send(i, &states[i])).collect();

        // 2. Build per-process inboxes according to HO set
        let inboxes: Vec<BTreeMap<usize, M>> = (0..n)
            .map(|receiver| {
                let mut inbox = BTreeMap::new();
                for sender in 0..n {
                    if ho(round, receiver, sender) {
                        inbox.insert(sender, messages[sender].clone());
                    }
                }
                inbox
            })
            .collect();

        // 3. All processes update (pure: old states -> new states)
        let new_states: Vec<S> = (0..n)
            .map(|i| update(i, &states[i], &inboxes[i], oracle(round, i)))
            .collect();

        states = new_states;
        check(round + 1, &states);
    }

    states
}

// ── Common HO (heard-of) strategies ────────────────────────────────

/// Reliable communication: every process hears every other process.
pub fn ho_reliable(_round: usize, _recv: usize, _send: usize) -> bool {
    true
}

/// Self-only delivery: each process hears only itself.
#[allow(dead_code)]
pub fn ho_self_only(_round: usize, recv: usize, send: usize) -> bool {
    recv == send
}

// ── Action-based simulator ─────────────────────────────────────────

/// Simulate an action-based protocol for `num_steps` steps.
///
/// Each step:
///   1. The `pick` callback selects an action from the possible actions.
///   2. If `can_fire(&state, &action)` holds, apply `step` to get the
///      new state and call `check` to assert invariants.
///   3. If `can_fire` is false, the action is skipped (stuttering step).
///
/// Returns the final state.
///
/// # Example
///
/// ```ignore
/// let final_state = run_actions(
///     LeaseState::init(3),
///     100,
///     |s| LeaseState::all_actions(s),    // enumerate possible actions
///     |s, a| s.can_fire(a),              // gate check
///     |s, a| s.fire(a),                  // pure transition
///     |step, _s, acts| acts[step % acts.len()].clone(), // round-robin pick
///     |step, s| { /* check invariants */ },
/// );
/// ```
pub fn run_actions<S: Clone, A: Clone>(
    init: S,
    num_steps: usize,
    actions: impl Fn(&S) -> Vec<A>,
    can_fire: impl Fn(&S, &A) -> bool,
    step: impl Fn(&S, &A) -> S,
    pick: impl Fn(usize, &S, &[A]) -> A,
    check: impl Fn(usize, &S),
) -> S {
    let mut state = init;
    check(0, &state);

    for i in 0..num_steps {
        let possible = actions(&state);
        if possible.is_empty() {
            continue;
        }
        let action = pick(i, &state, &possible);
        if can_fire(&state, &action) {
            state = step(&state, &action);
            check(i + 1, &state);
        }
    }

    state
}
