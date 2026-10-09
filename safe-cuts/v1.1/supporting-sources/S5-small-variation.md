# Independent review: position-sensitive band unfolding

Reviewed for Summer Bee, 20 September 2026. Input: `observatory_715_position_sensitive_followup`. The original packet was preserved. No Lean work or additional random search was performed.

**Verdict.** The twelve-panel certificate is valid. The all-cut positional identity is correct. I have neither proved nor refuted the universal implication

\[
|T_k|\le\pi\quad\Longrightarrow\quad\text{cut }k\text{ has pairwise disjoint panel interiors}.
\]

There is, however, a proved global implication that advances the mixed case: **mixed signs of the fixed-rim quantities \(T_k\) guarantee at least one safe cut.** This does not require the universal implication above. The unresolved part of that implication reduces to mutual separation of two explicitly selected strips, each already proved injective. The proofs and the remaining obligation follow below.

**What the twelve-panel certificate establishes.** The body is the convex hull of the packet's two rational input clouds at heights \(0\) and \(1/10000\), trimmed at relative depth \(1/100\). Its ordinary-band rims lie at \(1/1000000\) and \(99/1000000\). Exact supporting-plane checks give fourteen maximal original facets, including two caps, and twelve positive-area lateral panels. Exact projected hull tests confirm non-nesting.

The audit used the fixed **lower physical rim**, with its clockwise projected traversal. It did not switch rims between cuts.

| Claim | Independent check |
|---|---|
| Nonacute projected corners | All twelve corner scalar products are negative; the largest is \(-17/500\). |
| Mixed \(T\) signs | \(T_7>0\); the other eleven are negative. |
| Middle-window membership | Every \(|T_k|<\pi\); the smallest certified margin exceeds \(0.65\) radians. |
| No common forward direction for cut 0 | The three specified rim vectors have the positive determinant certificate stated in the packet. |
| All twelve cuts safe | 132 retained-neighbor opposite-side checks and 660 strict separating-axis checks pass. |

For the direction obstruction, with the packet's vectors \(u,v,w\), the exact identity

\[
\det(v,w)u+\det(w,u)v+\det(u,v)w=0
\]

has strictly positive coefficients, certified respectively greater than \(1/25,26,4\). A linear functional strictly positive on all three vectors would give a positive value on the left and zero on the right. Thus cut 0 genuinely has no common strictly forward linear projection.

The smallest certified unnormalized separating-axis gap is greater than \(4018/10000\). This is an algebraic gap for the axes used, not a normalized Euclidean distance. Retained neighbors are handled separately because they share their hinge.

The packet's 23 tests passed, the regenerated certificate matched the supplied JSON, and the source manifest was unchanged. The audit additionally checked the section hulls and angular signs with a different rational arctangent enclosure. This corroborates a finite exact certificate; the packet's numerical search counts play no role in the universal arguments below.

Evidence: audit results (`verification/audit_results.json`), test log (`verification/tests.log`), certificate log (`verification/certificate.log`), and independent arithmetic audit (`verification/independent_audit.log`), in the original review packet; these files are not included in this package.

**Fixed convention and inputs already established.** Write

\[
q_i=\beta_i-\pi,\qquad
\Delta=\sum_iq_i,\qquad
T_k=q_k-\Delta=-\sum_{i\ne k}q_i.
\]

These are real lifted quantities, not angles modulo \(2\pi\). Let \(\tau_i\) be the original projected exterior turn. I use the previously checked convex-band inequality

\[
|q_i|<\tau_i,\qquad \sum_i\tau_i=2\pi.
\tag{1}
\]

There is no repeated local-angle audit in this review. Nonacute projected corners additionally give \(\tau_i\le\pi/2\), but the new mixed-case argument below only needs (1).

Define the positive and negative turn variations

\[
P=\sum_i(q_i)_+,\qquad N=\sum_i(-q_i)_+.
\]

Then

\[
P+N<2\pi,\qquad \Delta=P-N.
\tag{2}
\]

At cut \(k\), the retained variations are

\[
P_k=P-(q_k)_+,\qquad N_k=N-(-q_k)_+.
\tag{3}
\]

The signed changes of developed rim heading are the \(q_i\), up to one common overall orientation reversal. Every argument using both variations is invariant under that one reversal. It never varies the convention from cut to cut.

**A proved geometric lemma: two small directional variations imply injectivity.** Consider any consecutive developed substrip. If its total positive turn and total negative turn are each strictly less than \(\pi\), that substrip is injective.

First lift its successive rim headings to real numbers \(\theta_0,\ldots,\theta_r\). Choose indices attaining the minimum and maximum. If the minimum comes first, their difference is at most the total positive turn; if the maximum comes first, it is at most the total negative turn. Hence

\[
\max\theta_i-\min\theta_i<\pi.
\]

The finitely many directions consequently admit a common linear coordinate \(X\) strictly increasing along every rim edge of this substrip. This coordinate has been **derived for the substrip under the stated hypothesis**.

To prove that this also controls positions, parameterize the strip using matched piecewise-linear rim coordinates \(s\) and normalized physical height \(t\):

\[
F(s,t)=(1-t)B(s)+tA(s),\qquad 0\le t\le1.
\]

Corresponding upper and lower rim edges of each trapezoid are positively parallel. Thus \(X_s>0\) inside every panel, at every height. The trapezoidal parameterization has nonzero Jacobian; consistent unfolding across retained hinges makes its sign the same on all panels.

Fix an \(X\)-coordinate \(x\). At each eligible height there is a unique \(s=s(x,t)\). The eligible heights form an interval: they are exactly those satisfying

\[
X(F(s_{\mathrm{left}},t))\le x\le X(F(s_{\mathrm{right}},t)),
\]

and both terminal-hinge coordinates are affine in \(t\). Normalize \(X\) and choose \(Y\) so that \((X,Y)\) is a positively oriented orthonormal coordinate system. Differentiation inside a panel gives

\[
\frac{d}{dt}Y(F(s(x,t),t))
=\frac{\det(F_s,F_t)}{X_s}.
\tag{4}
\]

This has one strict sign. The fixed-\(x\) trace is continuous across panel transitions, so its transverse coordinate is strictly monotone throughout its eligible height interval. If it runs along a hinge for an interval, the same conclusion follows by the one-sided formulas, or directly from that straight hinge. Thus two distinct heights cannot map to the same point; equal heights are already distinguished by strict increase in \(s\). This proves injectivity, including its positional content.

In particular,

\[
P_k<\pi\ \text{ and }\ N_k<\pi
\quad\Longrightarrow\quad\text{cut }k\text{ is safe}.
\tag{5}
\]

The twelve-panel example does not refute this lemma. It refutes deriving its hypothesis, or a common forward coordinate, for **every** middle-window cut.

**A justified global implication: the angularly mixed case has a safe cut.** If \(P,N<\pi\), (3) and (5) show that every cut is safe.

Otherwise, by (2) only one of \(P,N\) can reach \(\pi\). Suppose \(P\ge\pi\). Then \(N<\pi\) and \(\Delta=P-N>0\). Any cut with \(T_k\ge0\) satisfies

\[
q_k\ge\Delta>0,
\qquad
P_k=P-q_k\le P-\Delta=N<\pi,
\qquad
N_k=N<\pi.
\]

That cut is safe by (5). Equality \(T_k=0\) causes no problem because both retained variations are still strictly less than \(\pi\).

If \(N\ge\pi\), then \(P<\pi\) and \(\Delta<0\). A cut with \(T_k\le0\) has \(q_k\le\Delta<0\), so \(N_k=N+q_k\le N+\Delta=P<\pi\), while \(P_k=P<\pi\). That cut is safe. If \(\Delta=0\), both \(P=N<\pi\), already covered. This treats both signs without changing the physical rim or traversal convention.

Therefore, whenever negative and nonnegative \(T\) values both occur, a safe cut exists. In the genuinely two-sign case, a cut whose \(T_k\) has the same sign as \(\Delta\) works. This proves an angular mixed-case existence lemma without using the universal middle-window conjecture, an assumed global forward direction, or a numerical search.

For the twelve-panel specimen, rigorous rational enclosures give

\[
\begin{aligned}
3.52885217470185&<P<3.52885217470186,\\
2.12661436333599&<N<2.12661436333600,\\
1.40223781136585&<\Delta<1.40223781136586.
\end{aligned}
\]

Exactly cuts \(5,7,8,10\) satisfy (5). In particular, cut 7 is the witness selected by the mixed-case proof: \(T_7\approx0.03476917429>0\), \(P_7\approx2.091845189\), and \(N_7\approx2.126614363\). Cut 0 has \(P_0\approx3.528852175>\pi\), so the lemma makes no common-direction claim for it. Its safety comes from the separate positional certificate. Full enclosures are in retained turn budgets (`verification/retained_turn_budgets.json` in the original review packet; not included in this package).

**The position-sensitive identities remain exact.** Let \(P_i\) denote the positioned panel in the base development, and let the full-circuit isometry be \(H(x)=Qx+t\). After one common rigid alignment, cut \(k\) consists of

\[
P_k,\ldots,P_{n-1},H(P_0),\ldots,H(P_{k-1}).
\]

For \(i<j\), set \(J_{ij}=\{i+1,\ldots,j\}\), and retain the packet's collision predicates

\[
b_{ij}:\operatorname{int}P_i\cap\operatorname{int}P_j\ne\varnothing,
\qquad
c_{ij}:\operatorname{int}H(P_i)\cap\operatorname{int}P_j\ne\varnothing.
\]

The two panels are in the same circuit copy exactly when \(k\notin J_{ij}\). Hence

\[
\operatorname{Unsafe}(k)\iff
\exists i<j:\ (b_{ij}\land k\notin J_{ij})
\lor(c_{ij}\land k\in J_{ij}).
\tag{6}
\]

The translation \(t\) is essential. Nothing in this verification replaces \(H\) by its rotation or independently repositions stationary panels. In particular, a collision inside the common stationary block persists across neighboring cuts.

There are now additional restrictions on realizable predicates. For any set of intervening hinges \(J\), put

\[
P(J)=\sum_{\ell\in J}(q_\ell)_+,
\qquad N(J)=\sum_{\ell\in J}(-q_\ell)_+.
\]

The substrip lemma proves

\[
\begin{aligned}
b_{ij}&\Longrightarrow P(J_{ij})\ge\pi\ \text{or}\ N(J_{ij})\ge\pi,\\
c_{ij}&\Longrightarrow P(J_{ij}^{c})\ge\pi\ \text{or}\ N(J_{ij}^{c})\ge\pi.
\end{aligned}
\tag{7}
\]

Because \(P+N<2\pi\), every collision must consume at least \(\pi\) of the same globally dominant sign. In particular, **\(b_{ij}\) and \(c_{ij}\) cannot both hold for a genuine ordinary convex band**. Their disjoint intervening arcs would otherwise require at least \(2\pi\) total variation. The packet's observation that such an abstract Boolean assignment would block every cut is logically correct; (7) rules that assignment out geometrically.

Another consequence is that the baseline collision intervals \(J_{ij}\) with \(b_{ij}\) true have a nonempty common intersection. Each contains at least \(\pi\) dominant variation. Two disjoint such intervals would contradict (2), and a finite pairwise-intersecting family of ordinary intervals has a common intersection. This fact alone does not prevent the \(c\)-intervals from excluding individual middle-window cuts.

Two further restrictions apply to any collision witness:

- Its intervening original normal span is **strictly greater than \(\pi\)**. Indeed, its dominant variation is at least \(\pi\), while \(\sum_J\tau_i>\sum_J|q_i|\).
- Its points have **different physical heights**. At a fixed physical height, the developed horizontal section is a chain obtained from a convex section with the signed-turn bounds (1). Generalized Cauchy gives \(|D(p)-D(q)|\ge|p-q|>0\) for distinct points. This uses the corrected theorem in O'Rourke's [*On the Development of the Intersection of a Plane with a Polytope*, version 4](https://arxiv.org/pdf/cs/0006035v4), Theorem 1 and its slice application.

**The precise remaining geometric obligation.** Suppose a middle-window cut is not covered by (5). Fix the globally dominant sign once, and call its retained variation \(D_k\) and the other retained variation \(E_k\). Then necessarily

\[
\pi\le D_k<2\pi,\qquad 0\le E_k<\pi,
\qquad D_k-E_k=|T_k|\le\pi.
\tag{8}
\]

Thus this is specifically the case where at least \(\pi\) of turning in one sign is partially canceled by turning in the other sign. Cases with both retained variations below \(\pi\) have been proved safe.

List the panels in this cut's order. Select the **first retained hinge** at which cumulative dominant variation reaches or exceeds \(\pi\), and divide the panel chain at that hinge into a left block \(L\) and right block \(R\). The dividing hinge is internal to neither block.

The dominant variation internal to \(L\) is strictly less than \(\pi\), by the selection rule. The dominant variation internal to \(R\) is also strictly less than \(\pi\), because at least \(\pi\) has been consumed and \(D_k<2\pi\). Both blocks have minority variation less than \(\pi\). The substrip lemma therefore proves each block injective, with its own derived forward coordinate. Their two panels adjacent to the dividing hinge lie on opposite sides locally.

The smaller obligation is now:

> For two blocks obtained by this first-threshold split of a genuine ordinary convex band with nonacute projected corners, prove that (8) forces \(\operatorname{int}D(L)\cap\operatorname{int}D(R)=\varnothing\).

All possible failures are interactions **between** these two embedded strips. Any offending pair must satisfy (7), cross more than \(\pi\) of original normal span, and occur at unequal physical heights. Their placements are the actual placements in (6); the blocks may not be independently translated or rotated. Proving this cross-block separation would finish the universal middle-window implication, including its equality cases.

I have not proved that obligation. I also have not proved that a collision must meet one of the two outer cut hinges. Embedded equal-height chains and consistent local orientation, by themselves, do not supply that additional localization argument.

For clarity about the logical limit of the current restrictions, an **abstract, unrealized** nine-hinge assignment already separates the arithmetic from the missing geometry. Take \(\tau_i=2\pi/9\), \(q_1=\cdots=q_5=13/20\), and \(q_0=q_6=q_7=q_8=-33/50\). Then \(|q_i|<\tau_i\le\pi/2\), \(P=13/4\), \(N=66/25\), and \(\Delta=61/100\). Its \(T\) values are \(1/25\) at positive hinges and \(-127/100\) at negative hinges, so all are in the middle window and their signs are mixed. Assign only \(b_{0,5}\) true and every other collision predicate false. This satisfies the interval rule and all turn-budget restrictions above, yet (6) declares cut 0 unsafe. The mixed-case existence theorem is respected: cuts 1 through 5 remain safe.

This assignment is **not** a geometric counterexample: no corresponding convex band and positioned polygons have been supplied. It shows exactly why the scalar budgets plus the abstract cut-profile formula do not by themselves prove universal middle-window safety. The unresolved task is a geometric realizability/separation restriction, such as the cross-block obligation just stated.

**Relation to the thesis and the earlier audit.** The source is accessible here. I located the thesis and extracted figures in the research workspace and inspected printed pages 115 and 118, including Figures 7.15, 7.17, and 7.18. This is not a source-access failure. The thesis's passage from end directions to global nonoverlap is the mathematical issue under review. The new proof above does not silently treat that passage as established.

The packet's candidate definition of angular inversion is \(T_k<0\), using the fixed physical rim. The thesis instead describes inversion by a temporary inner/outer-chain switch in Figure 7.15. Their exact equivalence remains a separate matter. Accordingly, the proved statement here is an **angular mixed-case safe-cut theorem**. It supplies the desired existence conclusion for that precisely defined class, but I do not label it a complete reconstruction of the thesis's Lemma 7.14 or a new proof of all branches of Theorem 7.15.

Primary thesis: Greg Aloupis, [*Reconfigurations of Polygonal Structures*](https://central.bac-lac.gc.ca/.item?app=Library&id=TC-QMM-85114&oclc_number=894086208&op=pdf), Section 7.5. Local figures are available in the research workspace under `<research-record>/<historical-folder>` (not included).

The twelve-panel specimen is safe. No counterexample to the middle-window sufficient condition, and no counterexample to Theorem 7.15, has been produced. Even a future counterexample to the sufficient condition would only show that a particular middle-window cut can fail; it would not establish that every hinge of that band fails.
