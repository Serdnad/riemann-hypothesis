module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.FinPart
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1477
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SbSlice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev K1 (m n : ℕ) : Type := (Fin m × Fin n × Fin 2) ⊕ (Fin m × Fin 2)

def eK (m : ℕ) {n N : ℕ} (h : n + 1 = N) : K1 m n ≃ Fin m × Fin N × Fin 2 where
  toFun k := Sum.elim (fun p : Fin m × Fin n × Fin 2 => (p.1, em0 h p.2.1, p.2.2)) (fun p : Fin m × Fin 2 => (p.1, i0 h, p.2)) k
  invFun k := if hk : k.2.1.1 < n then Sum.inl (k.1, ⟨k.2.1.1, hk⟩, k.2.2) else Sum.inr (k.1, k.2.2)
  left_inv k := by
    rcases k with ⟨a, j, t⟩ | ⟨a, t⟩
    · simp [em0]
    · simp [i0]
  right_inv k := by
    obtain ⟨a, j, t⟩ := k
    by_cases hk : j.1 < n
    · simp [hk, em0]
    · have : j = i0 h := Fin.ext (by simp [i0]; omega)
      subst this
      simp [i0]

def ext0 {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) : Mx F E m N :=
  fun a i => if hi : i.1 < n then X a ⟨i.1, hi⟩ else 0

def frQ {m n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E) := w * ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) (b⁻¹).1)ᵀ

def emb {m n N : ℕ} (h : n + 1 = N) (b : GL (Fin n ⊕ Fin n) E) (bd : GL (Fin N ⊕ Fin N) E)
    (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin m) (Fin N ⊕ Fin N) (AE F E) :=
  ext0 h (frQ b w).toCols₁ * ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) bd.1.toCols₁)ᵀ + ext0 h (frQ b w).toCols₂ * ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) bd.1.toCols₂)ᵀ

def ChartFacts : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted (σ := σ) d.bs d.A d.Y d.b dd0 → IsAdapted (σ := σ) d.bs d.A Y b dd' →
    (∀ w', (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e (emb h b d.b w') =
      (Sum.elim (dd'.e w').1 (0 : Fin d.m × Fin 2 → AF F), Sum.elim (dd'.e w').2 (0 : Fin d.m × Fin 2 → AF F))) ∧
    (∀ u v : Fin d.m × Fin 2 → AF F, ∃ w, (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w =
      (Sum.elim (0 : Fin d.m × Fin n × Fin 2 → AF F) u, Sum.elim (0 : Fin d.m × Fin n × Fin 2 → AF F) v)) ∧
    (∀ g w, ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w).1 ∘ Sum.inl = 0 →
      ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w).2 ∘ Sum.inl = 0 → actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (j g) w = w) ∧
    (∀ g (w' : Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)), actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (j g) (emb h b d.b w') = emb h b d.b (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) g w')) ∧
    ∀ (u : UA σ d.A.J) (w' : Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)), mat u * emb h b d.b w' = emb h b d.b (mat u * w')

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

def sndHom (κ' κ'' A : Type) [AddCommGroup A] : (κ' ⊕ κ'' → A) →+ (κ'' → A) where
  toFun x := x ∘ Sum.inr
  map_zero' := rfl
  map_add' _ _ := rfl

theorem split_point {κ' κ'' A : Type} [AddCommGroup A] (x : κ' ⊕ κ'' → A) :
    x = Sum.elim (x ∘ Sum.inl) (0 : κ'' → A) + Sum.elim (0 : κ' → A) (x ∘ Sum.inr) := by
  funext i
  rcases i with i | i <;> simp

theorem finPart : FinPart := by
  intro F _ _ ψ hψ κ' κ'' _ _ a ha g hg hg0

  have H : ∀ N ∈ nhds (0 : κ' ⊕ κ'' → Af F), ∃ U : AddSubgroup (κ' ⊕ κ'' → Af F),
      IsOpen (U : Set (κ' ⊕ κ'' → Af F)) ∧ IsCompact (U : Set (κ' ⊕ κ'' → Af F)) ∧ (U : Set _) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ {χ : (κ' ⊕ κ'' → Af F) → ℂ | ∃ y : κ' ⊕ κ'' → Af F, χ = fun x => ψ (pairA F 0 (x ⬝ᵥ y))},
        (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1 := by
    intro N hN
    obtain ⟨U, hUo, hUc, hUN, hsep⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ (κ' ⊕ κ'') N hN
    refine ⟨U, hUo, hUc, hUN, fun x₀ hx₀ => ?_⟩
    obtain ⟨y, hyU, hy⟩ := hsep x₀ hx₀
    refine ⟨_, ⟨y, rfl⟩, fun u hu => ?_, hy⟩
    show ψ (pairA F 0 ((x₀ + u) ⬝ᵥ y)) = ψ (pairA F 0 (x₀ ⬝ᵥ y))
    rw [add_dotProduct, GlobalTheory.CharInvForm.pairA_zero_add, AddChar.map_add_eq_mul, hyU u hu, mul_one]

  obtain ⟨U₀, hU₀o, hU₀c, -, -, hper⟩ := GlobalTheory.CharForm.exists_periodic H hg Filter.univ_mem

  have hN'' : {u'' : κ'' → Af F | Sum.elim (0 : κ' → Af F) u'' ∈ U₀} ∈ nhds (0 : κ'' → Af F) := by
    have hc : Continuous fun u'' : κ'' → Af F => (Sum.elim (0 : κ' → Af F) u'' : κ' ⊕ κ'' → Af F) :=
      continuous_pi fun i => by rcases i with i | i <;> simp [continuous_const, continuous_apply]
    refine (hU₀o.preimage hc).mem_nhds ?_
    have : (Sum.elim (0 : κ' → Af F) (0 : κ'' → Af F) : κ' ⊕ κ'' → Af F) = 0 := by
      funext i; rcases i with i | i <;> rfl
    show Sum.elim (0 : κ' → Af F) (0 : κ'' → Af F) ∈ U₀
    rw [this]; exact U₀.zero_mem
  obtain ⟨U'', hU''o, -, hU''N, hsep''⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ'' _ hN''

  have hsc : Continuous (sndHom κ' κ'' (Af F)) := continuous_pi fun i => continuous_apply _
  set W : AddSubgroup (κ' ⊕ κ'' → Af F) := U''.comap (sndHom κ' κ'' (Af F)) with hW
  have hWo : IsOpen (W : Set (κ' ⊕ κ'' → Af F)) := hU''o.preimage hsc
  set P : AddSubgroup (κ' ⊕ κ'' → Af F) := U₀ ⊓ W with hP
  have hPo : IsOpen (P : Set (κ' ⊕ κ'' → Af F)) := by
    rw [hP, AddSubgroup.coe_inf]; exact hU₀o.inter hWo
  have hPc : IsCompact (P : Set (κ' ⊕ κ'' → Af F)) := by
    rw [hP, AddSubgroup.coe_inf]; exact hU₀c.inter_right (AddSubgroup.isClosed_of_isOpen W hWo)
  have hperP : ∀ x, ∀ u ∈ P, g (x + u) = g x := fun x u hu => hper x u (AddSubgroup.mem_inf.mp hu).1

  have : DiscreteTopology ((κ' ⊕ κ'' → Af F) ⧸ P) := QuotientAddGroup.discreteTopology hPo
  have hout : ∀ x : κ' ⊕ κ'' → Af F, g ((x : (κ' ⊕ κ'' → Af F) ⧸ P).out) = g x := fun x => by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add P x
    rw [hh]; exact hperP x h h.2
  have hfin : (QuotientAddGroup.mk '' tsupport g : Set ((κ' ⊕ κ'' → Af F) ⧸ P)).Finite :=
    (hg.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T : Finset ((κ' ⊕ κ'' → Af F) ⧸ P) := hfin.toFinset with hT
  have hsum : g = ∑ q ∈ T, g q.out • GlobalTheory.CharForm.cosetInd P q := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.CharForm.cosetInd, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · exact (hout x).symm
    · apply image_eq_zero_of_notMem_tsupport
      intro hxs
      exact hx (hfin.mem_toFinset.mpr ⟨x, hxs, rfl⟩)

  have hterm : ∀ q : (κ' ⊕ κ'' → Af F) ⧸ P, g q.out * a (GlobalTheory.CharForm.cosetInd P q) = 0 := by
    intro q
    by_cases hq : q.out ∘ Sum.inr ∈ U''
    · have h0 : g q.out = 0 := by
        rw [split_point q.out, hper _ _ (hU''N hq)]
        exact hg0 _
      rw [h0, zero_mul]
    · obtain ⟨y, hyU, hy⟩ := hsep'' _ hq
      set χ : (κ' ⊕ κ'' → Af F) → ℂ := fun x => ψ (pairA F 0 ((x ∘ Sum.inr) ⬝ᵥ y)) with hχ
      have hmul : (fun x => χ x * GlobalTheory.CharForm.cosetInd P q x) = χ q.out • GlobalTheory.CharForm.cosetInd P q := by
        funext x
        simp only [GlobalTheory.CharForm.cosetInd, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
        split_ifs with hxq
        · have hm : -q.out + x ∈ P := by
            rw [← QuotientAddGroup.out_eq' q] at hxq
            exact QuotientAddGroup.eq.mp hxq.symm
          have hmW : (-q.out + x) ∘ Sum.inr ∈ U'' := (AddSubgroup.mem_inf.mp hm).2
          have hx : x = q.out + (-q.out + x) := by abel
          rw [hx]
          show ψ (pairA F 0 ((q.out ∘ Sum.inr + (-q.out + x) ∘ Sum.inr) ⬝ᵥ y)) = ψ (pairA F 0 ((q.out ∘ Sum.inr) ⬝ᵥ y))
          rw [add_dotProduct, GlobalTheory.CharInvForm.pairA_zero_add, AddChar.map_add_eq_mul, hyU _ hmW, mul_one]
        · rfl
      have e := ha y _ (GlobalTheory.CharForm.cosetInd_mem_SB P hPo hPc q)
      rw [show (fun x => ψ (pairA F 0 ((x ∘ Sum.inr) ⬝ᵥ y)) * GlobalTheory.CharForm.cosetInd P q x) =
        χ q.out • GlobalTheory.CharForm.cosetInd P q from hmul, map_smul, smul_eq_mul] at e
      have : (χ q.out - 1) * a (GlobalTheory.CharForm.cosetInd P q) = 0 := by rw [sub_mul, e, one_mul, sub_self]
      rw [(mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hy), mul_zero]

  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [map_smul, smul_eq_mul, hterm q]

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

theorem partCharInv_of (hfin : FinPart) : PartCharInv := by
  intro F _ _ ψ hψ κ' κ'' _ _ l hl hinv Ψ hΨ hzero
  classical
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.CharInvForm.exists_schwartz_one (κ'' → mixedEmbedding.mixedSpace F)
  obtain ⟨U₀, hU₀o, hU₀c, -, -⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ'' Set.univ Filter.univ_mem
  set θf : (κ'' → Af F) → ℂ := GlobalTheory.CharForm.cosetInd U₀ 0 with hθf
  have hθfSB : θf ∈ SB (κ'' → Af F) := GlobalTheory.CharForm.cosetInd_mem_SB U₀ hU₀o hU₀c 0
  have hθf0 : θf 0 = 1 := by simp [hθf, GlobalTheory.CharForm.cosetInd]
  set θ : (κ'' → AF F) → ℂ := pureA F f₀ θf with hθ
  let P : ((κ' ⊕ κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' ⊕ κ'' → AF F) → ℂ) :=
    { toFun := fun Φ x => Φ (Sum.elim (x ∘ Sum.inl) 0) * θ (x ∘ Sum.inr)
      map_add' := fun _ _ => by funext x; simp [add_mul]
      map_smul' := fun _ _ => by funext x; simp [mul_assoc] }
  have hP : ∀ Φ x, P Φ x = Φ (Sum.elim (x ∘ Sum.inl) 0) * θ (x ∘ Sum.inr) := fun _ _ => rfl
  have e1 : ∀ x : κ' ⊕ κ'' → AF F, (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((Sum.elim (x ∘ Sum.inl) 0 : κ' ⊕ κ'' → AF F) i).1) =
      Sum.elim ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ∘ Sum.inl) 0 := by
    intro x; funext j; rcases j with j | j
    · rfl
    · simp only [Sum.elim_inr, Pi.zero_apply]
      exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have e2 : ∀ x : κ' ⊕ κ'' → AF F, (fun i => ((Sum.elim (x ∘ Sum.inl) 0 : κ' ⊕ κ'' → AF F) i).2) =
      Sum.elim ((fun i => (x i).2) ∘ Sum.inl) 0 := by
    intro x; funext j; rcases j with j | j <;> rfl
  have gen : ∀ (f : SchwartzMap (κ' ⊕ κ'' → mixedEmbedding.mixedSpace F) ℂ) (g : (κ' ⊕ κ'' → Af F) → ℂ),
      g ∈ SB (κ' ⊕ κ'' → Af F) → l (pureA F f g) = l (P (pureA F f g)) := by
    intro f g hg
    obtain ⟨fs, hfs⟩ := exists_slice (κ'' := κ'') f
    obtain ⟨f₁, hf₁⟩ := GlobalTheory.SchwartzBox.exists_schwartz_box fs f₀
    set g₁ : (κ' ⊕ κ'' → Af F) → ℂ := fun z => g (Sum.elim (z ∘ Sum.inl) 0) * θf (z ∘ Sum.inr) with hg₁def
    have hg₁ : g₁ ∈ SB (κ' ⊕ κ'' → Af F) := GlobalTheory.SchwartzBox.sb_box (sb_slice hg) hθfSB
    have hPf : P (pureA F f g) = pureA F f₁ g₁ := by
      funext x
      rw [hP]
      simp only [pureA, hθ, hf₁, hfs, hg₁def]
      rw [e1 x, e2 x]
      simp only [Function.comp_def]
      ring
    rw [hPf]
    obtain ⟨T, hT⟩ := hl g hg
    have hA : T f = T f₁ := by
      have h := arch_part T (fun L f₂ f₃ h23 => by
        obtain ⟨Y, hY⟩ := GlobalTheory.TraceDual.exists_trace_rep F κ'' L
        rw [← hT, ← hT, ← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0)
          (pureA F f₂ g) (GlobalTheory.CharInvForm.mem_schA f₂ hg)]
        congr 1
        funext x
        simp only [pureA, h23, GlobalTheory.CharInvForm.psi_dot_inf hψ, hY, Function.comp_def, mul_assoc]) (f - f₁) (fun v hv => by
          have hv' : v = Sum.elim (v ∘ Sum.inl) 0 := by
            funext j; rcases j with j | j
            · rfl
            · exact congrFun hv j
          rw [SchwartzMap.sub_apply, hf₁, hfs, hv, hf₀, mul_one]
          rw [← hv', sub_self])
      rw [map_sub, sub_eq_zero] at h
      exact h
    let a : ((κ' ⊕ κ'' → Af F) → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun h => l (pureA F f₁ h)
        map_add' := fun h h' => by
          rw [← map_add (f := _)]
          congr 1
          funext x
          simp [pureA, add_mul, mul_assoc, mul_comm, mul_left_comm]
        map_smul' := fun s h => by
          rw [RingHom.id_apply, ← map_smul]
          congr 1
          funext x
          simp [pureA, add_mul, mul_assoc, mul_comm, mul_left_comm] }
    have hB : a g = a g₁ := by
      have h := hfin F ψ hψ κ' κ'' a (fun y h hh => by
        show l (pureA F f₁ _) = l (pureA F f₁ h)
        rw [← hinv (fun i => pairA F 0 (y i)) (pureA F f₁ h) (GlobalTheory.CharInvForm.mem_schA f₁ hh)]
        congr 1
        funext x
        simp [pureA, GlobalTheory.CharInvForm.dot_pairA_fin, Function.comp_def, mul_left_comm]) (g - g₁) (sub_mem hg hg₁) (fun z' => by
          simp only [Pi.sub_apply, hg₁def, Sum.elim_comp_inl, Sum.elim_comp_inr, hθf0, mul_one, sub_self])
      rw [map_sub, sub_eq_zero] at h
      exact h
    calc l (pureA F f g) = T f := hT f
      _ = T f₁ := hA
      _ = l (pureA F f₁ g) := (hT f₁).symm
      _ = a g := rfl
      _ = a g₁ := hB
      _ = l (pureA F f₁ g₁) := rfl
  have key : ∀ Φ ∈ schA F (κ' ⊕ κ''), l Φ = l (P Φ) := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hmem =>
      obtain ⟨f, g, hg, rfl⟩ := hmem
      exact gen f g hg
    | zero => simp
    | add _ _ _ _ h h' => rw [map_add (f := _), map_add (f := _), map_add (f := _), h, h']
    | smul c _ _ h => rw [map_smul, map_smul, map_smul, h]
  have h0 : P Ψ = 0 := by
    funext x
    rw [hP, hzero, zero_mul]
    rfl
  rw [key Ψ hΨ, h0, map_zero]

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
end
