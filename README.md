# Lean Markov Chains

A work-in-progress formalization of undergraduate results in (finite
state-space) Markov chains in [Lean 4](https://lean-lang.org/).

## Outline

The project tries to maintain some level of semblance with the conventions of
Mathlib 4. The outline of the project folder is as follows:

- `Basic.lean` contains fundamental notions such as the transition matrix of a Markov chain (stochasticity) and probability vectors which can be acted upon by the aforementioned transition matrices.
- `Irreducible.lean` contains results on the irreducibility of Markov chains and
the reachability of states
- `Period.lean` contains results on the periodicity of states and importantly
the notion of an aperiodic chain.
- `Lazy.lean` contains helper theorems for the lazy chain $(I+P)/2$ generated
from the chain $P$.
- `Reversible.lean` contains results for reversible chains, in particular upper
bounding the convergence rate of $P^t$.
- `StationaryDistribution.lean` contains results for stationary distributions of chains (existence, uniqueness, positivity, etc.)
- `Spectral.lean` contains results on the spectral theory of Markov chains
(bounded eigenvalues, weak Perron-Frobenius, etc.)

## Goals

One big end goal for this project is formalizing the convergence and analysis of
some particular Markov chain (perhaps card shuffling?), but I haven't yet
decided what it should be. Other future goals include Markov chains for infinite
size state spaces via Markov kernels, hitting times, and and interfacing the
transition matrix probabilities with Mathlib probability theory.

## References

The following references were used for guidance in results on Markov chains.

- [1] David Asher Levin, Y Peres, E. L. Wilmer, J. Propp, and D. B. Wilson, Markov chains and mixing times. Providence, Rhode Island: American Mathematical Society, 2017.

- [2] G. Iyer, “Notes for 21-326: Markov Chains: Theory, Simulation and Applications,” math.cmu.edu, 2025. https://www.math.cmu.edu/~gautam/c/2025-326/notes/index.html (accessed Dec. 30, 2025).