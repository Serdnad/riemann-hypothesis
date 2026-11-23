module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwoAlt
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula
open GroundTheory.Automorphic.AutomorphicForm (constantTerm)

private theorem readJ_or {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {bad : Set (UpperTheory.V.Cj.S.Pl E)} {K W m₀}
    {X : Set (CuspSub E N)} {ι : Type} [Fintype ι] {P : ι → Sm E N → Prop} {Q : Sm E N → Prop}
    (h : ∀ i, ReadJ bad K W m₀ X (P i)) (hQ : ∀ φ, IsAutForm φ → Q φ → ∃ i, P i φ) : ReadJ bad K W m₀ X Q := by
  choose J i D C a b using h
  refine ⟨Σ i, J i, inferInstance, fun j => D j.1 j.2, fun j => C j.1 j.2, fun j => a j.1 j.2, fun φ m B h hm => ?_⟩
  choose c hc using fun k => hQ (φ k) (h k).1.aut (h k).2
  obtain ⟨i₀, h0⟩ := Finite.exists_infinite_fiber c
  have h1 : ∃ᶠ k in atTop, c k = i₀ := Nat.frequently_atTop_iff_infinite.2 (Set.infinite_coe_iff.1 h0)
  obtain ⟨σ, hσ, e⟩ := extraction_of_frequently_atTop h1
  obtain ⟨j, s, hs, hI, u⟩ := b i₀ (fun k => φ (σ k)) (fun k => m (σ k)) (fun k => B (σ k)) (fun k => ⟨(h _).1, e k ▸ hc _⟩)
    fun τ ε hε => hσ.tendsto_atTop.eventually (hm τ ε hε)
  exact ⟨⟨i₀, j⟩, fun k => σ (s k), hσ.comp hs, hI, u⟩

private theorem readJ_all (hC : CuspCaseJ) (hT : CtCaseJ) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {bad : Set (UpperTheory.V.Cj.S.Pl E)} (hb : bad.Finite) (N : ℕ) : ∀ K (W : Submodule ℂ (Kinf E N → ℂ)) m₀ (X : Set (CuspSub E N)),
    Lev bad K → FiniteDimensional ℂ W → (∀ π ∈ X, ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E N t * g) = ψ.1 g) →
    ReadJ bad K W m₀ X (Excl X) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro K W m₀ X hK hW hX
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨Unit, inferInstance, fun _ => CD.nil E, fun _ _ => 0, fun _ => ⟨fun π _ ⟨i, _⟩ => i.elim0,
      fun w _ => ⟨fun i => i.elim0, fun i => i.elim0, rfl⟩⟩, fun φ m B h hm => ⟨(), id, strictMono_id, ?_, fun w hw i => ?_⟩⟩
    · have e0 : m₀ = fun _ => 0 := by
        funext τ
        obtain ⟨k, hk⟩ := (hm τ 1 one_pos).exists
        have hc := Multiset.card_eq_card_of_rel hk
        rw [((h k).1.cap τ).1] at hc
        exact Multiset.card_eq_zero.1 hc.symm
      rw [e0]
      exact fun _ => rfl
    · have e : ∀ k, B k w = 0 := fun k => Multiset.card_eq_zero.1 ((h k).1.sat w hw).2.2.1
      simp only [e]
      exact tendsto_const_nhds
  have ih' : ∀ M < N, ∀ K (W : Submodule ℂ (Kinf E M → ℂ)) m₀, Lev bad K → FiniteDimensional ℂ W →
      ReadJ (N := M) bad K W m₀ ∅ fun _ => True := fun M hM K W m₀ hK hW =>
    readJ_or (ι := Unit) (fun _ => ih M hM K W m₀ ∅ hK hW fun _ h => h.elim) fun _ _ _ => ⟨(), fun _ h => h.elim⟩
  refine readJ_or (ι := Option {r : Fin N // 0 < r.1})
    (P := fun o φ => o.elim (IsCuspForm φ ∧ Excl X φ) fun r => ∃ g, constantTerm r.1.1 φ.1 g ≠ 0) ?_ fun φ ha hx => ?_
  · rintro (_ | ⟨⟨r, hr⟩, h0⟩)
    · exact hC E N hN bad K W m₀ X hb hK hW hX
    · obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
      have h0' : 0 < r := h0
      exact hT E r s h0' (by omega) bad (ih' r hr) (ih' s (by omega)) K W m₀ X hK hW
  · by_cases hc : IsCuspForm φ
    · exact ⟨none, hc, hx⟩
    · have h1 : ¬ GroundTheory.Automorphic.AutomorphicForm.IsCuspidal φ.1 := fun h2 =>
        hc ((UpperTheory.V.Cm.isCuspForm_iff φ).2 ⟨(UpperTheory.V.Cm.isAutForm_iff φ).1 ha, h2⟩)
      unfold GroundTheory.Automorphic.AutomorphicForm.IsCuspidal at h1
      push Not at h1
      obtain ⟨r, h0, hr, hg⟩ := h1
      exact ⟨some ⟨⟨r, hr⟩, h0⟩, hg⟩

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.cuspReadI_of :
    LevShrink → CuspCaseJ → CtCaseJ → CuspReadI := by
  intro hL hC hT E _ _ _ N K W bad m₀ X ho hW hb hl _ hX
  obtain ⟨K', hle, hK', -⟩ := hL E N bad K ho hl
  obtain ⟨J, i, D, C, a, b⟩ := readJ_all hC hT hb N K' W m₀ X hK' hW hX
  classical
  refine ⟨{j : J // (D j).Inf m₀}, inferInstance, fun j => D j.1, fun j => C j.1, fun j => a j.1, fun j => j.2,
    fun φ m B h hm => ?_⟩
  obtain ⟨j, s, hs, hI, u⟩ := b φ m B (fun k =>
    ⟨⟨(h k).1, (h k).2.1, ⟨fun u hu => (h k).2.2.1.1 u (hle hu), (h k).2.2.1.2⟩, (h k).2.2.2.1, (h k).2.2.2.2.1⟩,
      (h k).2.2.2.2.2⟩) hm
  exact ⟨⟨j, hI⟩, s, hs, u⟩
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem rel_comp {r s t : ℂ → ℂ → Prop} (h : ∀ x y z, r x y → s y z → t x z)
    {a b c : Multiset ℂ} (hab : Multiset.Rel r a b) :
    Multiset.Rel s b c → Multiset.Rel t a c := by
  induction hab generalizing c with
  | zero =>
    intro h0
    rw [Multiset.rel_zero_left] at h0
    subst h0
    exact Multiset.Rel.zero
  | cons hxy _ ih =>
    intro hc
    obtain ⟨z, zs, hz, hzs, rfl⟩ := Multiset.rel_cons_left.1 hc
    exact Multiset.Rel.cons (h _ _ _ hxy hz) (ih hzs)

private theorem exists_sep (S : Finset (ℂ × ℂ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ S, p.1 ≠ p.2 → ε < ‖p.1 - p.2‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert p S _ ih =>
    obtain ⟨ε, h0, hε⟩ := ih
    by_cases hp : p.1 = p.2
    · refine ⟨ε, h0, fun q hq hne => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact absurd hp hne
      · exact hε q hq hne
    · have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hp)
      refine ⟨min ε (‖p.1 - p.2‖ / 2), lt_min h0 (half_pos hpos), fun q hq hne => ?_⟩
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact (min_le_right _ _).trans_lt (half_lt_self hpos)
      · exact (min_le_left _ _).trans_lt (hε q hq hne)

private theorem eq_of_rel {a b : Multiset ℂ}
    (h : ∀ ε : ℝ, 0 < ε → Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) a b) : a = b := by
  classical
  obtain ⟨ε, h0, hε⟩ := exists_sep (a.toFinset ×ˢ b.toFinset)
  refine Multiset.rel_eq.1 ((h ε h0).mono fun x hx y hy hxy => ?_)
  by_contra hne
  exact absurd hxy (not_le.2 (hε (x, y) (by simp [hx, hy]) hne))

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.mtoLaws :
    MToLaws := by
  intro E _ _ _
  refine ⟨fun m x y hx hy => ?_, fun m x z z₀ hx hz τ ε hε => ?_,
    fun m m' x x' hx hx' τ ε hε => ?_⟩
  · funext τ
    refine eq_of_rel fun ε hε => ?_
    obtain ⟨k, h1, h2⟩ := ((hx τ (ε / 2) (half_pos hε)).and (hy τ (ε / 2) (half_pos hε))).exists
    refine rel_comp (fun p q w (hpq : ‖q - p‖ ≤ ε / 2) (hqw : ‖q - w‖ ≤ ε / 2) => ?_)
      (Multiset.rel_flip.2 h1) h2
    calc ‖p - w‖ = ‖(q - w) - (q - p)‖ := by congr 1; ring
      _ ≤ ‖q - w‖ + ‖q - p‖ := norm_sub_le _ _
      _ ≤ ε := by linarith
  · have hz' : ∀ᶠ k in atTop, ‖z k - z₀‖ ≤ ε / 2 :=
      (Metric.tendsto_nhds.1 hz (ε / 2) (half_pos hε)).mono fun k hk => by
        rw [dist_eq_norm] at hk
        exact hk.le
    filter_upwards [hx τ (ε / 2) (half_pos hε), hz'] with k h1 h2
    refine Multiset.rel_map.2 (h1.mono fun p _ q _ hpq => ?_)
    calc ‖(p + z k) - (q + z₀)‖ = ‖(p - q) + (z k - z₀)‖ := by congr 1; ring
      _ ≤ ‖p - q‖ + ‖z k - z₀‖ := norm_add_le _ _
      _ ≤ ε := by linarith
  · filter_upwards [hx τ ε hε, hx' τ ε hε] with k h1 h2
    exact h1.add h2
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.ctCaseJ :
    StepT → SplitLim → SatComb → CDAddG → AbsInf → MToLaws → CtCaseJ := by
  intro hS hL hC hA hI hM E _ _ _ r s hr hs bad ih₁ ih₂ K W m₀ X hK hW
  obtain ⟨K₁, W₁, K₂, W₂, l₁, f₁, l₂, f₂, hS⟩ := hS E r s bad K W hK hW
  obtain ⟨T, hT⟩ := hL E m₀ ((-((s : ℝ) / 2) : ℝ) : ℂ) (((r : ℝ) / 2 : ℝ) : ℂ)
  choose J₁ i₁ D₁ C₁ a₁ b₁ using fun p : T => ih₁ K₁ W₁ p.1.1 l₁ f₁
  choose J₂ i₂ D₂ C₂ a₂ b₂ using fun p : T => ih₂ K₂ W₂ p.1.2 l₂ f₂
  have hν := fun x : ℝ => GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) x
  choose D d₁ d₂ d₃ using fun j : Σ p : T, J₁ p × J₂ p => hA E r s (D₁ j.1 j.2.1) (D₂ j.1 j.2.2)
    (GlobalTheory.Mem.Chr.CharModel.absChar E ((-((s : ℝ) / 2) : ℝ) : ℂ)) (GlobalTheory.Mem.Chr.CharModel.absChar E (((r : ℝ) / 2 : ℝ) : ℂ)) hr hs
  refine ⟨Σ p : T, J₁ p × J₂ p, inferInstance, D, _, fun j => ⟨fun π _ => d₁ j π, fun w hw =>
    d₂ j w _ _ ((hν _).1 w) ((hν _).1 w) ((a₁ j.1 j.2.1).2 w hw) ((a₂ j.1 j.2.2).2 w hw)⟩, fun φ m B h hm => ?_⟩
  choose φ₁ φ₂ m₁ m₂ B₁ B₂ e₁ e₂ e₃ e₄ using fun k => hS (φ k) (m k) (B k) (h k).1 (h k).2
  obtain ⟨p, hp, σ, hσ, t₁, t₂⟩ := hT m m₁ m₂ e₃ hm
  obtain ⟨j₁, σ₁, hσ₁, v₁, u₁⟩ := b₁ ⟨p, hp⟩ (fun k => φ₁ (σ k)) _ (fun k => B₁ (σ k)) (fun k => ⟨e₁ _, trivial⟩) t₁
  obtain ⟨j₂, σ₂, hσ₂, v₂, u₂⟩ := b₂ ⟨p, hp⟩ (fun k => φ₂ (σ (σ₁ k))) (fun k => m₂ (σ (σ₁ k))) (fun k => B₂ (σ (σ₁ k)))
    (fun k => ⟨e₂ _, trivial⟩) fun τ ε hε => hσ₁.tendsto_atTop.eventually (t₂ τ ε hε)
  have h₀ : m₀ = fun t => (p.1 t).map (· + ((-((s : ℝ) / 2) : ℝ) : ℂ)) + (p.2 t).map (· + (((r : ℝ) / 2 : ℝ) : ℂ)) := by
    obtain ⟨hu, hsh, hadd⟩ := hM E
    have c₁ := hsh _ _ (fun _ => ((-((s : ℝ) / 2) : ℝ) : ℂ)) _ t₁ tendsto_const_nhds
    have c₂ := hsh _ _ (fun _ => (((r : ℝ) / 2 : ℝ) : ℂ)) _ t₂ tendsto_const_nhds
    have c₃ := hadd _ _ _ _ c₁ c₂
    refine hu (fun k => m (σ k)) _ _ (fun τ ε hε => hσ.tendsto_atTop.eventually (hm τ ε hε)) ?_
    have : (fun k => m (σ k)) = fun k t => (m₁ (σ k) t).map (· + ((-((s : ℝ) / 2) : ℝ) : ℂ)) +
        (m₂ (σ k) t).map (· + (((r : ℝ) / 2 : ℝ) : ℂ)) := by
      funext k t
      exact e₃ _ t
    rw [this]
    exact c₃
  refine ⟨⟨⟨p, hp⟩, j₁, j₂⟩, fun k => σ (σ₁ (σ₂ k)), hσ.comp (hσ₁.comp hσ₂), fun τ => ?_, fun w hw => ?_⟩
  · rw [d₃ ⟨⟨p, hp⟩, j₁, j₂⟩ τ, h₀]
    have key : ∀ (n : ℕ) (D' : CD E n) (z : ℝ) (x : (E →+* ℂ) → Multiset ℂ), D'.Inf x →
        ∑ i, ((D'.P i).twist (GlobalTheory.Mem.Chr.CharModel.absChar E (z : ℂ))).infChar τ = (x τ).map (· + (z : ℂ)) := by
      intro n D' z x hx
      rw [← hx τ]
      simp only [fun i => ((hI E _ (D'.P i) (z : ℂ) τ).2)]
      exact (map_sum (Multiset.mapAddMonoidHom (· + (z : ℂ))) _ _).symm
    exact congrArg₂ (· + ·) (key _ _ _ _ v₁) (key _ _ _ _ v₂)
  have := hC.2 (qV E w) r s _ _ _ _ ((GlobalTheory.Mem.Chr.CharModel.absChar E ((-((s : ℝ) / 2) : ℝ) : ℂ)).val w)
    ((GlobalTheory.Mem.Chr.CharModel.absChar E (((r : ℝ) / 2 : ℝ) : ℂ)).val w) (qV_ne_zero w)
    (fun i => (u₁ w hw i).comp hσ₂.tendsto_atTop) (u₂ w hw)
  intro i
  refine (this i).congr fun k => ?_
  exact congrArg (fun M => satEig (qV E w) (r + s) M i) (e₄ _ _ _ (hν _) (hν _) w hw).symm
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.regOf :
    MWAt → DualWt → RegOf := by
  intro mw dw E _ _ _ n l D hD τ
  have hτ := hD τ
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · refine ⟨l (InfinitePlace.mk τ), ?_⟩
    have h1 := (mw E n l (InfinitePlace.mk τ)).1
    rw [h] at h1
    rw [hτ, h1]
  · obtain ⟨lam, hlam⟩ := dw n (l (InfinitePlace.mk τ))
    refine ⟨lam, ?_⟩
    have hc : ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding = τ := by
      rw [h]
      ext x
      simp [ComplexEmbedding.conjugate_coe_eq]
    have h2 := (mw E n l (InfinitePlace.mk τ)).2
    rw [hc] at h2
    rw [hτ, h2, hlam]
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem sum_map_eq {ι : Type} [Fintype ι] (f : ι → Multiset ℂ) (g : ℂ → ℂ) :
    ∑ i, (f i).map g = (∑ i, f i).map g :=
  (map_sum (Multiset.mapAddMonoidHom g) f Finset.univ).symm

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.twDataT :
    CDAddG → MuInf → MWAt → DualWt → TwDataT := by
  intro hAdd hMu hMW hDW E _ _ _ n a b hab ha hb μ e hμ l₁ l₂ lam hlam D₁ D₂ h₁ h₂
  subst hab
  obtain ⟨D, hnot, hsat, hinf⟩ := hAdd E a b D₁ D₂ (μ ^ b) (μ ^ a) ha hb
  have hval : ∀ (w : Pl E) (k : ℕ), (μ ^ k).val w = μ.val w ^ k :=
    fun w k => MonoidHom.pow_apply μ.1 k _
  have hunr : ∀ {w : Pl E} (k : ℕ), μ.UnrAt w → (μ ^ k).UnrAt w := by
    intro w k h x hx
    have e1 : (μ ^ k).loc w x = μ.loc w x ^ k := MonoidHom.pow_apply μ.1 k _
    rw [e1, h x hx, one_pow]
  have hT := (hMu E μ e hμ).2
  have hemb : ∀ {m : ℕ} (C : CD E m) (l : InfinitePlace E → DomWeight m) (k : ℕ), C.Inf (mW l) →
      ∀ v : InfinitePlace E, ∑ i, ((C.P i).twist (μ ^ k)).infChar v.embedding =
        (infOfWeight (l v)).map (· + (k : ℂ) * (e v : ℂ) / 2) := by
    intro m C l k hC v
    have h1 : ∀ i, ((C.P i).twist (μ ^ k)).infChar v.embedding =
        ((C.P i).infChar v.embedding).map (· + (k : ℂ) * (e v : ℂ) / 2) :=
      fun i => (hT (C.N i) k (C.P i) v).1
    simp only [h1]
    rw [sum_map_eq, hC v.embedding, (hMW E m l v).1]
  have hcon : ∀ {m : ℕ} (C : CD E m) (l : InfinitePlace E → DomWeight m) (k : ℕ), C.Inf (mW l) →
      ∀ v : InfinitePlace E, ∑ i, ((C.P i).twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) =
        (infOfWeight (l v)).map (fun t => -(t + (k : ℂ) * (e v : ℂ) / 2)) := by
    intro m C l k hC v
    have h1 : ∀ i, ((C.P i).twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) =
        ((C.P i).infChar (ComplexEmbedding.conjugate v.embedding)).map (· - (k : ℂ) * (e v : ℂ) / 2) :=
      fun i => (hT (C.N i) k (C.P i) v).2
    simp only [h1]
    rw [sum_map_eq, hC (ComplexEmbedding.conjugate v.embedding), (hMW E m l v).2, Multiset.map_map]
    refine Multiset.map_congr rfl fun t _ => ?_
    simp only [Function.comp_apply]
    ring
  refine ⟨D, hnot, ?_, ?_⟩
  · intro τ
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · refine ⟨lam (InfinitePlace.mk τ), ?_⟩
      rw [hinf τ, ← hlam (InfinitePlace.mk τ), ← hemb D₁ l₁ b h₁, ← hemb D₂ l₂ a h₂, h]
    · obtain ⟨lam', hl⟩ := hDW (a + b) (lam (InfinitePlace.mk τ))
      have hτ : τ = ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding := by
        rw [h]
        exact (star_star τ).symm
      refine ⟨lam', ?_⟩
      rw [hinf τ, hl, ← hlam (InfinitePlace.mk τ), Multiset.map_add (f := _), Multiset.map_map, Multiset.map_map]
      have e1 := hcon D₁ l₁ b h₁ (InfinitePlace.mk τ)
      have e2 := hcon D₂ l₂ a h₂ (InfinitePlace.mk τ)
      rw [← hτ] at e1 e2
      rw [e1, e2]
      rfl
  · intro w B₁ B₂ hu s₁ s₂
    have h := hsat w B₁ B₂ (hunr b hu) (hunr a hu) s₁ s₂
    rw [hval, hval] at h
    exact h
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem inv_map_sign (B : Multiset ℂˣ) (k : ℕ) (h : inv B = B) :
    inv (B.map (· * (-1 : ℂˣ) ^ k)) = B.map (· * (-1 : ℂˣ) ^ k) := by
  have hk : ((-1 : ℂˣ) ^ k)⁻¹ = (-1 : ℂˣ) ^ k := by
    rw [← inv_pow, inv_neg_one]
  conv_rhs => rw [← h]
  simp only [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [Function.comp_apply, mul_inv, hk]

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.unStable :
    UnStable := by
  intro E _ _ _ μ a b w B₁ B₂ hμ h₁ h₂
  have hadd : ∀ X Y : Multiset ℂˣ, inv (X + Y) = inv X + inv Y := fun X Y => Multiset.map_add _ _ _
  simp only [un, hμ]
  rw [hadd, inv_map_sign B₁ b h₁, inv_map_sign B₂ a h₂]
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.absInf :
    AbsInf := by
  intro E _ _ _ N P z τ
  have key : (P.twist (Model.absC E z)).infChar τ = (P.infChar τ).map (· + z) := by
    have e := ((ParLaws.hasInfChar_infChar P τ).twist (Model.absC E z)).infChar_eq
    rw [Model.expo_absC] at e
    exact e
  exact ⟨key, key⟩
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.csdInert :
    GOne.CsdSat → CsdInert := by
  intro h E _ _ _ n hn π hd
  filter_upwards [h E n hn π hd] with w hw hns B hB
  obtain ⟨B₀, hB₀, hc⟩ := hw
  obtain rfl := CG.HasSat.unique hB hB₀
  exact CG.HasSat.unique (hc w ⟨rfl, Or.inr hns⟩) hB
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.cdAddG :
    CDAddG := by
  intro E _ _ _ r s D₁ D₂ ν ν' hr hs
  let e : Fin (D₁.c + D₂.c) ≃ Fin D₁.c ⊕ Fin D₂.c := finSumFinEquiv.symm
  let Q : Fin D₁.c ⊕ Fin D₂.c → Σ k, CG E k := Sum.elim (fun i => ⟨_, (D₁.P i).twist ν⟩) fun i => ⟨_, (D₂.P i).twist ν'⟩
  refine ⟨⟨D₁.c + D₂.c, fun i => (Q (e i)).1, fun i => (Q (e i)).2, fun i => ?_, ?_⟩, fun π hπ => ?_,
    fun w B₁ B₂ h h' ⟨b₁, c₁, d₁⟩ ⟨b₂, c₂, d₂⟩ => ⟨fun i => Sum.elim (fun i => (b₁ i).map (· * ν.val w))
      (fun i => (b₂ i).map (· * ν'.val w)) (e i), fun i : Fin (D₁.c + D₂.c) => ?_, ?_⟩, fun τ => ?_⟩
  · rcases e i with i | i
    exacts [D₁.pos i, D₂.pos i]
  · rw [e.sum_comp fun o => (Q o).1, Fintype.sum_sum_type]
    exact congrArg₂ (· + ·) D₁.sum D₂.sum
  · obtain ⟨i, hi⟩ := hπ
    have h1 : (Q (e i)).1 = r + s := congrArg Sigma.fst hi
    revert h1
    rcases e i with i | i
    · intro h1
      have h2 : D₁.N i ≤ r := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans D₁.sum.le
      have h3 : D₁.N i = r + s := h1
      omega
    · intro h1
      have h2 : D₂.N i ≤ s := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans D₂.sum.le
      have h3 : D₂.N i = r + s := h1
      omega
  · show (Q (e i)).2.HasSat w (Sum.elim (fun i => (b₁ i).map (· * ν.val w)) (fun i => (b₂ i).map (· * ν'.val w)) (e i))
    rcases e i with i | i
    exacts [PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ h (c₁ i), PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ h' (c₂ i)]
  · show ∑ i : Fin (D₁.c + D₂.c), _ = _
    rw [e.sum_comp (Sum.elim (fun i => (b₁ i).map (· * ν.val w)) fun i => (b₂ i).map (· * ν'.val w)), Fintype.sum_sum_type,
      ← d₁, ← d₂]
    exact congrArg₂ (· + ·) (map_sum (Multiset.mapAddMonoidHom _) _ _).symm (map_sum (Multiset.mapAddMonoidHom _) _ _).symm
  · show ∑ i : Fin (D₁.c + D₂.c), (Q (e i)).2.infChar τ = _
    rw [e.sum_comp fun o => (Q o).2.infChar τ, Fintype.sum_sum_type]
    rfl
end
