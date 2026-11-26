# Phi-closure mathematical erratum

Base: `47c55209be5d6aea4b15b2cbeab4a40af451cfef`.

Source: [phi_descent_closure_conditional.tex](final_wall/phi_descent_closure_conditional.tex).

The displayed hypotheses are inconsistent under the convention that $\lambda_1$ is the lowest eigenvalue and $\Delta=\operatorname{div}\nabla$. On a closed gradient shrinking soliton with $\mu>0$, the scalar curvature satisfies $\Delta_f s=2\mu s-2|\operatorname{Ric}|^2$, where $\Delta_f=\Delta-\nabla f\cdot\nabla$. At a scalar-curvature minimum this excludes a negative minimum. A zero minimum forces $s\equiv0$ by the strong maximum principle applied to $(\Delta_f-2\mu)s\le0$, contradicting the integrated trace identity $\int_M s=3\mu\operatorname{Vol}(M)$. Hence $s>0$ and the Rayleigh quotient gives $\lambda_1(-4\Delta+s)\ge\min_M s>0$. Consequently $\Phi(g_\ast)<0$, contradicting assumption 2. The stated conditional implication is vacuous. Moreover, the proof does not establish that the limiting soliton is Einstein or justify the topology of a limit after surgery. This argument does not supply a Poincare derivation. The independently verified local combinatorial results are unaffected.

Historical statement retained. Paper analysis only; no Lean or PDF changes.
