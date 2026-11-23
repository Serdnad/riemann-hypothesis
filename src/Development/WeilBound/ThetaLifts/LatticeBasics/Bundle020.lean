module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle018
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {B : Base F E} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χ χ' : Chr F E} {o : Rep σ Y W} {r s r' s' : ℕ}

theorem conv_of_cpt (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) : ∀ Φ ∈ schA F _, M.Conv o Φ := by
  intro Φ hΦ h
  obtain ⟨t1, t2, -⟩ := (hT F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).1 Φ hΦ
  have hc : Continuous fun g => theta o Φ g h := t1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ := c.bdd hc fun γ hγ g => by simpa using t2 γ hγ 1 (one_mem _) g h
  exact Measure.integrableOn_of_bounded (M := C) (c.fin _ _ p.good.haar p.good.dom).ne hc.aestronglyMeasurable
    (Eventually.of_forall hC)

theorem I_lin (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (hΨ : Ψ ∈ schA F _) (a : ℂ) : M.I o (Φ + a • Ψ) = M.I o Φ + a • M.I o Ψ := by
  funext h
  have e : ∀ g, theta o (Φ + a • Ψ) g h = theta o Φ g h + a * theta o Ψ g h := fun g => by
    simp only [theta, map_add (f := _), map_smul]
    rw [thetaSum_add F (p.weil.isUSplitting.pres _ _ hΦ) (Submodule.smul_mem _ _ (p.weil.isUSplitting.pres _ _ hΨ)),
      thetaSum_smul]
  simp only [Model.I, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add (conv_of_cpt hT p c _ hΦ h) ((conv_of_cpt hT p c _ hΨ h).const_mul a), integral_const_mul]

theorem pol_sch (hM : M.IsGood B.ψ) : PolData B M ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ h1 ((h2.and hM.std).mono fun _ h => h.1.trans h.2)

theorem int_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}
    (h : IsFundamentalDomain Γ D μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) :
    ∫ x in D, f (x * g) ∂μ = ∫ x in D, f x ∂μ := by
  have h' : IsFundamentalDomain Γ ((fun x => x * g) '' D) μ := by
    simpa [← Set.image_smul] using h.smul_of_comm (MulOpposite.op g)
  rw [← (measurePreserving_mul_right μ g).setIntegral_image_emb (Homeomorph.mulRight g).measurableEmbedding f D]
  exact h'.setIntegral_eq h fun γ x => hf γ γ.2 x

theorem I_act (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) {Φ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (g : UA σ Y.J) : M.I o (o (g, 1) Φ) = M.I o Φ := by
  funext h
  obtain ⟨-, t2, -⟩ := (hT F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p).1 Φ hΦ
  haveI := c.cnt
  haveI := p.good.haar
  haveI := c.right _ p.good.haar
  have e : ∀ x, theta o (o (g, 1) Φ) x h = theta o Φ (x * g) h := fun x => by
    rw [theta, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [Model.I, e]
  exact int_right p.good.dom (fun x => theta o Φ x h)
    (fun γ hγ x => by simpa using t2 γ hγ 1 (one_mem _) x h) g

theorem upd_sb {v : Pl F} {φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {z} (hz : z ∈ SB _) (u : Pl F) :
    Function.update φ v z u ∈ SB _ := by
  by_cases e : u = v
  · subst e; rwa [Function.update_self]
  · rw [Function.update_of_ne e]; exact h u

theorem upd_cof {v : Pl F} {φ φ' : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = φ' u) (z) :
    ∀ᶠ u in cofinite, Function.update φ v z u = φ' u :=
  (h.and (eventually_cofinite_ne v)).mono fun _ e => by rw [Function.update_of_ne e.2]; exact e.1

theorem I_aug (hT : ThetaBasic) (p : IsPair B M χ χ' o r s r' s') (c : Cpt σ Y.J) (v : Pl F) (f : SInf F (Fin n × Fin d))
    {φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = M.vac u)
    {z₀ z} (h0 : z₀ ∈ SB _) (hz : z ∈ augAt o v) :
    M.I o (pure f (Function.update φ v (z₀ + z))) = M.I o (pure f (Function.update φ v z₀)) := by
  have h3 := (h2.and p.good.std).mono fun _ h => h.1.trans h.2
  obtain ⟨t, ht, ht'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ h3
  have mem : ∀ z ∈ SB _, pure f (Function.update φ v z) ∈ schA F _ := fun z hz =>
    GlobalTheory.TensUniq.pure_mem_schA f _ (upd_sb h1 hz) (upd_cof h3 z)
  have add : ∀ z ∈ SB _, ∀ z' ∈ SB _, ∀ a : ℂ, M.I o (pure f (Function.update φ v (z + a • z'))) =
      M.I o (pure f (Function.update φ v z)) + a • M.I o (pure f (Function.update φ v z')) := fun z hz z' hz' a => by
    rw [← I_lin hT p c (mem z hz) (mem z' hz'), ← ht', ← ht', ← ht']
    congr 1
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have zero : M.I o (pure f (Function.update φ v 0)) = 0 := by
    have := add 0 (zero_mem _) 0 (zero_mem _) (-1)
    simpa using this
  have key : z ∈ SB _ ∧ M.I o (pure f (Function.update φ v z)) = 0 := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, -, x, hx, y, hy, a, rfl⟩ := hz
      refine ⟨sub_mem hy hx, ?_⟩
      have e := a t ⟨ht, ht' x ▸ mem x hx⟩
      rw [ht', ht'] at e
      rw [sub_eq_add_neg, ← neg_one_smul ℂ x, add y hy x hx, ← e, I_act hT p c (mem x hx)]
      simp
    | zero => exact ⟨zero_mem _, zero⟩
    | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, by simpa [hx.2, hy.2] using add x hx.1 y hy.1 1⟩
    | smul a x _ hx => exact ⟨Submodule.smul_mem _ _ hx.1, by simpa [hx.2, zero] using add 0 (zero_mem _) x hx.1 a⟩
  simpa [key.2] using add z₀ h0 z key.1 1

theorem toSo_of (hR : KReal) (hF : KFin) (hK : KCoinv) (hT : ThetaBasic) (hC : CptAll) : ToSo := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h hq Φ' hΦ
  obtain ⟨R, hr⟩ := hR F E σ B a a' G X om om' h
  obtain ⟨Rf, hf⟩ := hF F E σ B a a' G X om om' h
  obtain ⟨-, k1, k2, -⟩ := (hK F E σ B a a' G X om om' R Rf ⟨h, hr, hf⟩).1 _ h.chars.good
  have p := pairV' h
  have c := hC F E σ B _ _ _ _ h.base (.inl p.herm) (by omega)
  have le := pol_sch p.good
  induction hΦ using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hz
    obtain ⟨y, hy, e⟩ := k2 B.τ₁ (Rf.p' _ (φ B.v₁))
    refine ⟨pure f (Function.update φ B.v₁ y), ⟨Submodule.subset_span ⟨f, hf, _, upd_sb h1 hy.1, upd_cof h2 y, rfl⟩,
      Submodule.subset_span ⟨f, _, upd_sb h1 hy.1, upd_cof h2 y, by rwa [Function.update_self], rfl⟩⟩, ?_⟩
    have := I_aug hT p c B.v₁ f h1 h2 hy.1 ((k1 _ (sub_mem (h1 _) hy.1)).1 (by rw [map_sub, e, sub_self]))
    rw [← this, add_sub_cancel, Function.update_eq_self]
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add x y hx hy ix iy =>
    obtain ⟨x', mx, ex⟩ := ix
    obtain ⟨y', my, ey⟩ := iy
    refine ⟨x' + y', add_mem mx my, ?_⟩
    rw [← one_smul ℂ y, ← one_smul ℂ y', I_lin hT p c (le mx.1) (le my.1), I_lin hT p c (le hx) (le hy), ex, ey]
  | smul t x hx ix =>
    obtain ⟨x', mx, ex⟩ := ix
    refine ⟨t • x', Submodule.smul_mem _ _ mx, ?_⟩
    rw [← zero_add (t • x), ← zero_add (t • x'), I_lin hT p c (zero_mem _) (le mx.1), I_lin hT p c (zero_mem _) (le hx), ex]

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_ext {ι : Type} (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module ℂ (M v)] {S T : Finset ι} (h : S ⊆ T)
    (z : ∀ v, M v) : ∃ e : (PiTensorProduct ℂ fun v : S => M v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T => M v,
      ∀ u : ∀ v, M v, (∀ v ∉ S, u v = z v) → e (PiTensorProduct.tprod ℂ fun v : S => u v) = PiTensorProduct.tprod ℂ fun v : T => u v := by
  let c : (∀ v : S, M v) → ∀ v : T, M v := fun x v => if hv : (v : ι) ∈ S then x ⟨v, hv⟩ else z v
  have key : ∀ [DecidableEq S] x (i : S) w, c (Function.update x i w) = Function.update (c x) ⟨i, h i.2⟩ w := fun x i w => by
    funext v
    by_cases hvi : v = ⟨i, h i.2⟩
    · subst hvi
      simp [c]
    · rw [Function.update_of_ne hvi]
      by_cases hv : (v : ι) ∈ S
      · simp only [c, dif_pos hv]
        exact Function.update_of_ne (fun e => hvi (Subtype.ext (by rw [← e]))) _ _
      · simp only [c, dif_neg hv]
  refine ⟨PiTensorProduct.lift
    { toFun := fun x => PiTensorProduct.tprod ℂ (c x)
      map_update_add' := fun x i y y' => by simp only [key]; exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
      map_update_smul' := fun x i a y => by simp only [key]; exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }, fun u hu => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  refine congrArg (PiTensorProduct.tprod ℂ) (funext fun v => ?_)
  by_cases hv : (v : ι) ∈ S
  · simp only [c, dif_pos hv]
  · simp only [c, dif_neg hv, hu v hv]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d a a' : ℕ}
  {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}


variable (B G R Rf) in
def On (T : Finset (Pl F)) (Φ : Fn F a (a + a')) (Φ' : Fn F a' (a + a')) : Prop :=
  ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

theorem On.mono (hm : IsMatched B G X om om' R Rf) {S T : Finset (Pl F)} (h0 : X.T ⊆ S) (h : S ⊆ T) {Φ Φ'}
    (H : On B G R Rf S Φ Φ') : On B G R Rf T Φ Φ' := by
  obtain ⟨m, m', f, φ, f', φ', h1, h2, e1, e2, e3⟩ := H
  obtain ⟨e, he⟩ := exists_ext Rf.Pi h fun v => Rf.p v (G.M.vac v)
  refine ⟨m, m', f, φ, f', φ', fun i => ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun k => hv (h k)⟩,
    fun i => ⟨(h2 i).1, (h2 i).2.1, fun v hv => (h2 i).2.2 v fun k => hv (h k)⟩, e1, e2, ?_⟩
  have := congrArg (e.lTensor R.Pi) e3

  simp only [map_sum, LinearMap.lTensor_tmul] at this
  refine (Finset.sum_congr rfl fun i _ => ?_).trans (this.trans (Finset.sum_congr rfl fun i _ => ?_))
  · rw [he (fun v => Rf.p v (φ i v)) fun v hv => by rw [(h1 i).2.2 v hv]]
  · rw [he (fun v => Rf.p' v (φ' i v)) fun v hv => by rw [(h2 i).2.2 v hv, (hm.fin.sph v fun k => hv (h0 k)).1]]

theorem pm_zero : PolMatch B G X R Rf 0 0 :=
  ⟨_, le_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp, by simp, by simp⟩

theorem pm_add (hm : IsMatched B G X om om' R Rf) {Φ Φ' Ψ Ψ'} (c : ℂ) (h1 : PolMatch B G X R Rf Φ Φ')
    (h2 : PolMatch B G X R Rf Ψ Ψ') : PolMatch B G X R Rf (c • Φ + Ψ) (c • Φ' + Ψ') := by
  obtain ⟨T₁, hT₁, H₁⟩ := h1
  obtain ⟨T₂, hT₂, H₂⟩ := h2
  obtain ⟨m, m', f, φ, f', φ', hf, hf', rfl, rfl, e1⟩ := On.mono hm hT₁ (Finset.subset_union_left (s₂ := T₂)) H₁
  obtain ⟨k, k', g, ψ, g', ψ', hg, hg', rfl, rfl, e2⟩ := On.mono hm hT₂ (Finset.subset_union_right (s₁ := T₁)) H₂
  refine ⟨T₁ ∪ T₂, hT₁.trans Finset.subset_union_left, m + k, m' + k', Fin.append (c • f) g, Fin.append φ ψ, Fin.append (c • f') g',
    Fin.append φ' ψ', fun i => ?_, fun i => ?_, funext fun x => ?_, funext fun x => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply]
      exact ⟨Submodule.smul_mem _ _ (hf i).1, (hf i).2⟩
    · simp only [Fin.append_right]
      exact hg i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply]
      exact ⟨Submodule.smul_mem _ _ (hf' i).1, (hf' i).2⟩
    · simp only [Fin.append_right]
      exact hg' i
  · simp [Fin.sum_univ_add, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum, mul_assoc]
  · simp [Fin.sum_univ_add, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum, mul_assoc]
  · rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, map_smul, ← TensorProduct.smul_tmul']
    rw [← Finset.smul_sum, ← Finset.smul_sum, e1, e2]

theorem loc_op (hS : SplitModel) {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {o : Rep σ Y W} {χ χ' : Chr F E} {r s r' s' : ℕ}
    (p : IsPair B M χ χ' o r s r' s') {v : Pl F} (t : E →ₐ[F] Fv F v) {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) :
    ∃ O : Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ), (∀ φ ∈ SB _, O φ ∈ SB _ ∧ Acts (evFin F v) (o (1, h)) φ (O φ)) ∧
      ∀ f (φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ), (∀ u, φ u ∈ SB _) → (∀ᶠ u in cofinite, φ u = M.vac u) →
        o (1, h) (pure f φ) = pure f (Function.update φ v (O (φ v))) := by
  obtain ⟨-, ι, b, -, r1⟩ := hS F E σ B n d Y W M _ _ o _ _ _ _ p v t
  obtain ⟨j, -, j2⟩ := exists_inv' b
  let h₀ := Matrix.GeneralLinearGroup.map (piW t) h.1
  have k := fun φ hφ => acts_of_reads (r1 h hh h₀ rfl) j2 (φ := φ) hφ
  refine ⟨j ∘ₗ GlobalTheory.SplitFlip.repB (chrW χ' t) (chrW χ t) (1, h₀) ∘ₗ ι, k, fun f φ p1 p2 => ?_⟩
  obtain ⟨T, t1, -, t3⟩ := intersection_update_fsHerm_neg_one v f p1 ((p2.and p.good.std).mono fun _ h => h.1.trans h.2)
  have := t3 _ _ (p1 v) _ (k _ (p1 v)).2
  rwa [t1, t1, Function.update_eq_self] at this

theorem pm_fin (hS : SplitModel) (hm : IsMatched B G X om om' R Rf) {v : Pl F} (t : E →ₐ[F] Fv F v) {h : UA σ G.W.J}
    (hh : h ∈ UAt σ G.W (evFin F v)) {Φ Φ'} (H : PolMatch B G X R Rf Φ Φ') :
    PolMatch B G X R Rf (om (1, h) Φ) (om' (1, h) Φ') := by
  obtain ⟨T, hT, H⟩ := H
  obtain ⟨m, m', f, φ, f', φ', h1, h2, rfl, rfl, e⟩ := On.mono hm hT (Finset.subset_insert v T) H
  obtain ⟨O, o1, o2⟩ := loc_op hS (pairV hm.triple) t hh
  obtain ⟨O', o1', o2'⟩ := loc_op hS (pairV' hm.triple) t hh
  obtain ⟨s, hs⟩ := ((Rf.p v).domRestrict (SB _)).exists_rightInverse_of_surjective
    ((LinearMap.range_domRestrict _ _).trans (hm.fin.onto v))
  let A : Module.End ℂ (Rf.Pi v) := Rf.p v ∘ₗ O ∘ₗ (SB _).subtype ∘ₗ s
  have q : ∀ x ∈ SB _, ∀ x' ∈ SB _, Rf.p v x = Rf.p' v x' → Rf.p v (O x) = Rf.p' v (O' x') := fun x hx x' hx' =>
    hm.fin.equiv v h hh x hx x' hx' _ (o1 x hx).1 _ (o1' x' hx').1 (o1 x hx).2 (o1' x' hx').2
  have A' : ∀ x' ∈ SB _, A (Rf.p' v x') = Rf.p' v (O' x') := fun x' hx' =>
    q _ (s _).2 x' hx' (LinearMap.congr_fun hs _)
  have A1 : ∀ x ∈ SB _, A (Rf.p v x) = Rf.p v (O x) := fun x hx => by
    obtain ⟨x', hx', k⟩ : Rf.p v x ∈ (SB _).map (Rf.p' v) := hm.fin.onto' v ▸ Submodule.mem_top
    rw [q x hx x' hx' k.symm, ← k, A' x' hx']
  have up : ∀ {P : ∀ u : Pl F, Type} (Q : ∀ u, P u → Prop) (x : ∀ u, P u) (y : P v), Q v y → (∀ u ≠ v, Q u (x u)) →
      ∀ u, Q u (Function.update x v y u) := fun Q x y a b u => by
    by_cases hu : u = v
    · subst hu; rwa [Function.update_self]
    · rw [Function.update_of_ne hu]; exact b u hu
  have ne : ∀ u ∉ insert v T, u ≠ v := fun u hu k => hu (k ▸ Finset.mem_insert_self _ _)
  refine ⟨_, hT.trans (Finset.subset_insert v T), m, m', f, fun i => Function.update (φ i) v (O (φ i v)), f',
    fun i => Function.update (φ' i) v (O' (φ' i v)), fun i => ⟨(h1 i).1,
      up (fun u x => x ∈ SB _) _ _ (o1 _ ((h1 i).2.1 v)).1 fun u _ => (h1 i).2.1 u,
      fun u hu => (Function.update_of_ne (ne u hu) _ _).trans ((h1 i).2.2 u hu)⟩, fun i => ⟨(h2 i).1,
      up (fun u x => x ∈ SB _) _ _ (o1' _ ((h2 i).2.1 v)).1 fun u _ => (h2 i).2.1 u,
      fun u hu => (Function.update_of_ne (ne u hu) _ _).trans ((h2 i).2.2 u hu)⟩, ?_, ?_, ?_⟩

  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => o2 _ _ (h1 i).2.1 ((insert v T).eventually_cofinite_notMem.mono (h1 i).2.2)

  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => o2' _ _ (h2 i).2.1 ((insert v T).eventually_cofinite_notMem.mono (h2 i).2.2)
  let D : ∀ u, Module.End ℂ (Rf.Pi u) := Function.update (fun _ => LinearMap.id) v A
  have := congrArg ((PiTensorProduct.map fun u : (insert v T : Finset _) => D u).lTensor R.Pi) e

  simp only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod] at this
  refine (Finset.sum_congr rfl fun i _ => ?_).trans (this.trans (Finset.sum_congr rfl fun i _ => ?_)) <;> congr 2 <;> funext ⟨u, _⟩ <;>
    by_cases hu : u = v
  · subst hu; simp only [D, Function.update_self, A1 _ ((h1 i).2.1 _)]
  · simp only [D, Function.update_of_ne hu, LinearMap.id_apply]
  · subst hu; simp only [D, Function.update_self, A' _ ((h2 i).2.1 _)]
  · simp only [D, Function.update_of_ne hu, LinearMap.id_apply]

end GlobalTheory.ThK.Dbl.TC

end
end
