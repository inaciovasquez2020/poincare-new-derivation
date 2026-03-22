# Poincaré Conjecture — New Derivation Attempt

**Status:** Conditional / Not proven.

## Scope

A combinatorial descent program on triangulated closed simply connected 3-manifolds.

## Core object

For a finite triangulation \(T\) of a closed 3-manifold, define
\[
\Phi(T)=\sum_{v\in T}|d(v)-6|,
\]
where \(d(v)\) is the number of tetrahedra incident to \(v\).

## Admissible local moves

\[
\mathcal M=\{(1\leftrightarrow 4),(2\leftrightarrow 3)\}.
\]

These preserve homeomorphism type.

## Structural program

1. Define admissible Pachner-type local moves.  
2. Define a defect functional \(\Phi\).  
3. Prove strict local descent: \(\exists T'\) with \(\Phi(T')<\Phi(T)\) for non-spherical \(T\).  
4. Prove finite termination.  
5. Prove \(\Phi(T)=0\) characterizes the spherical model.

## Current state

Intermediate claims include unproved or false steps.

## Minimal valid status

Conditional on:

- Local spherical descent lemma:
\[
\forall T\not\simeq S^3,\ \exists T'\in\mathcal M(T)\ \text{s.t.}\ \Phi(T')<\Phi(T).
\]

- Zero-defect characterization:
\[
\Phi(T)=0 \;\Longrightarrow\; T\simeq S^3.
\]

## Repository additions

- Hypergraph Final Wall (Chronicles), conditional closure.  
- EF-signature invariant and non-collision lemma.  
- Structured collision experiments (near-injective regime).  
- Spectral correction: HS operator requires squared resolvent decay.  

