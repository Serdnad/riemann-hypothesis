module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle058
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupHeightLeTwoGoodReduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.PsiStep

section Red
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem q_mem : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal

theorem q_ne_zero : ((qOf P : ℕ) : E) ≠ 0 := by
  have h : qOf P ≠ 0 := by
    unfold qOf
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  exact_mod_cast h

theorem intAt_q : IntAt P (qOf P : E) := by
  have := IntAt.coe P ((qOf P : ℕ) : 𝓞 E)
  rwa [map_natCast] at this

theorem reduction_natCast_eq_zero : redP P (qOf P : E) = 0 := by
  have := reduction_coe P ((qOf P : ℕ) : 𝓞 E)
  rw [map_natCast] at this
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (q_mem P)

theorem pow_red (k : ℕ) : IntAt P ((qOf P : E) ^ (k + 1)) ∧ redP P ((qOf P : E) ^ (k + 1)) = 0 := by
  induction k with
  | zero =>
    rw [zero_add, pow_one]
    exact ⟨intAt_q P, reduction_natCast_eq_zero P⟩
  | succ k ih =>
    rw [pow_succ]
    exact ⟨ih.1.mul (intAt_q P), by rw [reduction_mul ih.1 (intAt_q P), ih.2, zero_mul]⟩

theorem reduction_one' : redP P (1 : E) = 1 := by
  have := reduction_coe P 1
  rwa [map_one, map_one] at this

theorem valuation_one₂ : LocE.vP P (qOf P) (1 : E) = 0 := by
  have hq0 := q_ne_zero P
  have hex : ∃ z : ℤ, IsUnit (redP P ((1 : E) / (qOf P : E) ^ z)) :=
    ⟨0, by rw [zpow_zero, div_one, reduction_one']; exact isUnit_one⟩
  have hspec : IsUnit (redP P ((1 : E) / (qOf P : E) ^ LocE.vP P (qOf P) (1 : E))) := by
    unfold LocE.vP
    exact Classical.epsilon_spec hex
  by_contra hne
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (LocE.vP P (qOf P) (1 : E))
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, zpow_natCast] at hspec
    by_cases hI' : IntAt P ((1 : E) / (qOf P : E) ^ (k' + 1))
    · have e : (qOf P : E) ^ (k' + 1) * (1 / (qOf P : E) ^ (k' + 1)) = 1 := by field_simp
      have h0 : redP P ((qOf P : E) ^ (k' + 1) * (1 / (qOf P : E) ^ (k' + 1))) = 0 := by
        rw [reduction_mul (pow_red P k').1 hI', (pow_red P k').2, zero_mul]
      rw [e, reduction_one'] at h0
      exact one_ne_zero h0
    · rw [reduction_eq_zero_of_not_integral P hI'] at hspec
      exact not_isUnit_zero hspec
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, one_mul, (pow_red P k').2] at hspec
    exact not_isUnit_zero hspec

theorem locChar_one_ne {K : Type} [Field K] (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) :
    LocE.locChar (qOf P) cq χ (1 : E) ≠ 0 := by
  unfold LocE.locChar
  rw [valuation_one₂, zpow_zero, zpow_zero, one_mul, div_one]
  unfold LocE.unitV
  rw [dite_eq_left (by rw [reduction_one']; exact isUnit_one)]
  exact Units.ne_zero _

end Red

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge.PsiStep

section Mat
variable {E : Type} [Field E]

theorem joinCol_apply {n' c' n c : ℕ} (x₀ : HomE E n' n) (y' : Sp E n) (v : Fin (n' + c') → E) (i : Fin n) :
    joinCol (c' := c') (c := c) x₀ y' v (Fin.castAdd c i) =
      x₀ (fun l => v (Fin.castAdd c' l)) i + atNL E (n' + c') n' v * y' i := by
  simp [joinCol, Loc.inX, LinearMap.funLeft]
  rfl

end Mat

theorem om_one_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (Φ : Matrix b a k → ℂ) :
    om μ 1 1 Φ = Φ := by
  funext x
  simp [om, nabs]

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge.PsiStep

theorem withCol_toLoc {E k : Type} [Field E] [NumberField E] [StarRing E]
    [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k)
    {A B : Type} {n' n c' c : ℕ} (e : A ≃ Fin n) (e' : B ≃ Fin n') (hc' : c' = 0 + 1) (hc : c = 0)
    (x₀ : HomE E n' n) (y' : Sp E n) :
    withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι ((e.sumCongr (finCongr hc.symm)).trans finSumFinEquiv) ((e'.sumCongr (finCongr hc'.symm)).trans finSumFinEquiv)
        (joinCol (c' := c') (c := c) x₀ y') := by
  subst hc' hc
  ext (r | r) (j | j)
  · simp only [withCol, fromBlocks_apply₁₁, toLoc, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, joinCol_apply]
    have h1 : (fun l : Fin n' => (Pi.single (Fin.castAdd (0 + 1) (e' j)) (1 : E) : Fin (n' + (0 + 1)) → E)
        (Fin.castAdd (0 + 1) l)) = Pi.single (e' j) 1 := by
      funext l
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
    have h2 : atNL E (n' + (0 + 1)) n' (Pi.single (Fin.castAdd (0 + 1) (e' j)) 1) = 0 := by
      have hj := (e' j).isLt
      unfold atNL
      rw [dite_eq_left (by omega)]
      simp only [LinearMap.coe_proj, Function.eval, Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
      rw [if_neg (by omega)]
    rw [h1, h2, zero_mul, add_zero]
  · simp only [withCol, fromBlocks_apply₁₂, toLoc, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, joinCol_apply]
    have h1 : (fun l : Fin n' => (Pi.single (Fin.natAdd n' (finCongr (rfl : 0 + 1 = 0 + 1) j)) (1 : E) : Fin (n' + (0 + 1)) → E)
        (Fin.castAdd (0 + 1) l)) = 0 := by
      funext l
      have hl := l.isLt
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, Pi.zero_apply]
      rw [if_neg (by omega)]
    have h2 : atNL E (n' + (0 + 1)) n' (Pi.single (Fin.natAdd n' (finCongr (rfl : 0 + 1 = 0 + 1) j)) 1) = 1 := by
      unfold atNL
      rw [dite_eq_left (by omega)]
      simp only [LinearMap.coe_proj, Function.eval, Pi.single_apply, Fin.ext_iff, Fin.val_natAdd]
      rw [if_pos (by omega)]
    rw [h1, map_zero, Pi.zero_apply, h2, one_mul]
    rw [zero_add (y' (e r))]
    rfl
  · exact r.elim0
  · exact r.elim0

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge.PsiStep

section Main
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem omPhi_one_one (i : ℕ) (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i P 1 1 x = PhiAt Ch mu cst.sharp i P.1 x := by
  have hm : muAt Ch sel mu cst i P 1 ≠ 0 := by
    unfold muAt
    exact locChar_one_ne _ _ _
  unfold omPhi Loc.om
  rw [map_one, map_one, Units.val_one, valuation_one₂]
  rw [mul_inv_cancel₀ hm]
  simp only [neg_zero, zero_mul, zpow_zero, one_mul]
  rfl

end Main

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge


open PsiStep in
theorem psiAgree_of_atType : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → PsiAgree Ch sel mu cst σ₀ P ι S := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν _ hA e' e he' he
  have hc1 : cOf R s = 0 + 1 := by unfold cOf; rw [hA.steps]; omega
  have hc0 : cOf R (s + 1) = 0 := by unfold cOf; rw [hA.steps]; omega
  have hrS : R.rS = S.ρ := by
    have := S.odd
    unfold Ranks.rS; rw [hA.steps]; omega
  have hr : R.r = R.k + s + 1 := by unfold Ranks.r; rw [hA.steps]; omega
  let E' : XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1) ≃ Fin (R.N s + cOf R s) :=
    (e'.sumCongr (finCongr hc1.symm)).trans finSumFinEquiv
  let E₁ : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (e.sumCongr (finCongr hc0.symm)).trans finSumFinEquiv
  have hE' : IsOrd (yPos xPos (R.N s)) E' := by
    rintro (a | a)
    · simp [E', yPos, he' a]
    · simp [E', yPos]
  have hE₁ : IsOrd (yPos xPos (R.N (s + 1))) E₁ := by
    rintro (a | a)
    · simp [E₁, yPos, he a]
    · exact a.elim0
  have hPhi := GlobalTheory.T.symLevelTestFunctions_agree_rationalPoints X.E X.K k P.1 (qOf P.1) ι σ₀ (psi0P Ch P.1) (chiP Ch P.1) s R.k S hA.tie
    R.t s 0 rfl (R.N s) (cOf R s) (R.N (s + 1)) (cOf R (s + 1)) rfl rfl hc1 hc0 E' E₁ hE' hE₁
  refine ⟨1, one_ne_zero, fun x₀ y' => ?_⟩
  have hmat : withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') := by
    exact withCol_toLoc ι e e' hc1 hc0 x₀ y'
  rw [one_mul, Chain.Psi, om_one_one, hmat, hPhi, PsiAt, omPhi_one_one]
  unfold PhiAt
  rw [if_pos hA.mem, if_pos hA.sharp, hrS, hr]

end GlobalTheory.SymBridge
end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.TopAgree
variable {E K k : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdOrd_top {κ τ s : ℕ} (b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 1)) :
    ∃ b', stdOrd (Fin κ) (Fin τ) (s + 1) 0 rfl b = Sum.inl b' ∧ xPos b' = zPos b := by
  rcases b with (i | i) | p
  · exact ⟨_, stdOrd_eps _ _ _ _ _ i, rfl⟩
  · have h := stdOrd_f (Fin κ) (Fin τ) (s + 1) 0 rfl i
    have e : (⟨0 + i.val, by omega⟩ : Fin (s + 1)) = i := Fin.ext (by simp)
    rw [e] at h
    exact ⟨_, h, rfl⟩
  · exact ⟨_, stdOrd_d _ _ _ _ _ p, rfl⟩

theorem top_entries (q : ℕ) (ι : E →+* k) {s κ : ℕ} (S : SymData k s κ) (τ n' n : ℕ)
    (e' : XIx (Fin κ) (Fin τ) (s + 1) ⊕ Fin 0 ≃ Fin (n' + 0)) (e : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin (n + 0))
    (he' : IsOrd (yPos xPos n') e') (he : IsOrd zPos e) (x : (Fin (n' + 0) → E) →ₗ[E] (Fin (n + 0) → E)) :
    (S.T (Fin τ)).PhiTop (toLoc ι e e' x) = S.P.iterPhi (Fin τ) S.μ S.tame (s + 1)
      (Matrix.of fun a b => ι (LocE.entB q κ 0 n' 0 n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b))) := by
  simp only [SymData.T, typeChain, Chain.ofType, LatFrame.transport, LatFrame.coords]
  congr 1
  have hb : (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) (s + 1) 0 rfl)).bas.val = 1 := by
    ext (u | u) (v | v)
    · simp [typeFrame, embA, Matrix.one_apply]
    · exact v.elim0
    · exact u.elim0
    · exact u.elim0
  ext a b
  obtain ⟨b', hb1, hb2⟩ := stdOrd_top (κ := κ) (τ := τ) (s := s) b
  have ha : zPos a < n := by have := (e a).isLt; rw [he a] at this; omega
  have hb' : zPos b < n' := by
    have := (e' (Sum.inl b')).isLt; rw [he' (Sum.inl b')] at this; simp [yPos] at this; omega
  have h1 : ∀ p N, (if p < κ then p else if p < κ + 0 then N + (p - κ) else p - 0) = p := by
    intro p N; split_ifs <;> omega
  rw [hb]
  simp only [LatFrame.refl, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.submatrix_apply, id,
    Equiv.refl_apply, Matrix.of_apply, typeFrame, hb1, toLoc, LocE.entB, LocE.fIdx, LocE.scE, h1, if_pos ha, if_pos hb',
    sub_self, zpow_zero, mul_one, Loc.atN, dif_pos (show zPos a < n + 0 from ha)]
  have hv : (Pi.single (e' (Sum.inl b')) 1 : Fin (n' + 0) → E) = Loc.eN E (n' + 0) (zPos b) := by
    funext l
    simp only [Loc.eN, Pi.single_apply, Fin.ext_iff, he' (Sum.inl b'), yPos, Sum.elim_inl, hb2]
  rw [hv, show e a = ⟨zPos a, by omega⟩ from Fin.ext (he a)]

theorem bottom_iff {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} (hC : IsCompl P q ι ϖ)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (κ l τ j : ℕ) (M : ℕ → ℕ → E) :
    MaxM ((Matrix.of fun a b => ι (M (zPos a) (zPos b)) :
        Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) (j + 1)) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k).submatrix
          (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j) id).toRows₂ ↔
      ∀ p p', κ + l + j * τ ≤ p → p < κ + l + (j + 1) * τ → p' < κ + l + j * τ → IntAt P (M p p' / (q : E)) := by
  have res := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU
  constructor
  · intro h p p' hp hp' hp''
    have := h ⟨p - (κ + l + j * τ), by rw [Nat.add_mul] at hp'; omega⟩ ((zEquiv κ l τ j).symm ⟨p', hp''⟩)
    simp only [Matrix.toRows₂, Matrix.submatrix_apply, id, Matrix.of_apply, zPos_ixSucc_inr] at this
    rw [← zEquiv_val, Equiv.apply_symm_apply] at this
    rw [← (res.1 _)]
    convert this using 4
    omega
  · intro h u b
    simp only [Matrix.toRows₂, Matrix.submatrix_apply, id, Matrix.of_apply, zPos_ixSucc_inr]
    rw [res.1]
    exact h _ _ (by omega) (by rw [Nat.add_mul]; omega) (zPos_lt b)

theorem unit_char {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {σ₀ : K →+* ℂ} {ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K}
    {χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ} {s κ : ℕ} {S : SymData k s κ} (hT : Comparison₂ P q ι σ₀ ψ₀ χ S) (i : ℕ) (d : E) (u : kˣ)
    (hd : IntAt P d) (hu : valuation k (u : k) = 1) (e : (u : k) = ι d) :
    (S.μ (i + 1) u : ℂ) = σ₀ (LocE.unitV (χ i) d) := by
  have res := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι S.ϖ hT.compl S.unif
  exact hT.chi i d u hd ((res.2.2.1 d hd).1 (e ▸ hu)) e

theorem intAt_div {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {a : E} (h : IntAt P (a / (q : E))) (hq : (q : E) ≠ 0) :
    IntAt P a := by
  have := h.mul (IntAt.coe P (q : 𝓞 E))
  simpa [div_mul_cancel₀ _ hq] using this

theorem core (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {s κ : ℕ} (S : SymData k s κ) (hT : Comparison₂ P q ι σ₀ ψ₀ χ S) (τ j N : ℕ)
    (hN : N = κ + s + 1 + (j + 1) * τ) (M : ℕ → ℕ → E) :
    S.P.iterPhi (Fin τ) S.μ S.tame j (Matrix.of fun a b => ι (M (zPos a) (zPos b))) =
      σ₀ (phiM q ψ₀ χ κ S.ρ (κ + s + 1) τ j N M) := by
  subst hN
  have hC := hT.compl
  have res := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι S.ϖ hC S.unif
  have hq : (q : E) ≠ 0 := res.2.2.2.1
  have hpat := GlobalTheory.T.symmetricLevelChain_pattern_iterated k s κ S (Fin τ) j
  set T : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k :=
    Matrix.of fun a b => ι (M (zPos a) (zPos b)) with hTdef
  have hTop : ((Matrix.of fun a b => ι (M (zPos a) (zPos b)) :
      Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k).submatrix
        (ixSucc (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) id).toRows₁ = T := by
    ext a b; simp [Matrix.toRows₁, hTdef, zPos_ixSucc_inl]
  have hB := bottom_iff hC S.unif κ (s + 1) τ j M

  have hpatM := GlobalTheory.T.symChainPattern_iff_place_conditions E k P q ι S.ϖ hC S.unif κ (s + 1) S.ρ τ j M
  have hKO := GlobalTheory.T.mem_integralGL_iff_isUnit_det_at_prime E k P q ι S.ϖ hC S.unif κ (s + 1) τ j M
  simp only [TypeDatum.iterPhi, TypeDatum.Phi, hTop]
  unfold phiM
  by_cases hb : MaxM ((Matrix.of fun a b => ι (M (zPos a) (zPos b)) :
      Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k).submatrix
        (ixSucc (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) id).toRows₂
  swap
  · rw [if_neg hb, if_neg, map_zero]
    rintro ⟨-, h2, -⟩
    exact hb (hB.2 fun p p' h1 h1' h1'' => h2 p p' h1 (by rw [Nat.add_mul] at h1' ⊢; omega) h1'')
  rw [if_pos hb]
  have h2 := hB.1 hb
  have hzT : ∀ a b, T a b = ι (M (zPos a) (zPos b)) := fun a b => rfl
  have hdet : ∀ g : GL (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k, g.val = T →
      ((Matrix.GeneralLinearGroup.det g : kˣ) : k) =
        ι (Matrix.det (Matrix.of fun s' s'' : Fin (κ + s + 1 + j * τ) => M s'.1 s''.1)) := by
    intro g hg
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hTdef,
      det_of_places ι (zEquiv κ (s + 1) τ j) zPos 0 (fun x => by simp [zEquiv_val]) M]
    simp only [zero_add]
    rfl
  have hintdet : ∀ g : GL (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k, g ∈ KO k _ → g.val = T →
      IntAt P (Matrix.det (Matrix.of fun s' s'' : Fin (κ + s + 1 + j * τ) => M s'.1 s''.1)) := by
    intro g hg hgT
    rw [← hC.int, ← hdet g hgT, Valuation.mem_integer_iff, valuation_det_of_mem_KO hg]
  by_cases hJ : ∃ g ∈ (S.P.iter (Fin τ) S.μ S.tame j).J, g.val = T
  · obtain ⟨g, hgJ, hgT⟩ := hJ
    obtain ⟨hgKO, hgpat⟩ := (hpat g).1 hgJ
    obtain ⟨hint, -⟩ := hKO.1 ⟨g, hgKO, hgT⟩
    have hpat' : ∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j),
        ¬FreeIx S.ρ a b → (valuation k) (ι (M (zPos a) (zPos b)) -
          (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k) a b) < 1 := by
      intro a b hf; have := hgpat a b hf; rwa [hgT] at this
    obtain ⟨h3, h4⟩ := (hpatM hint).1 hpat'
    have hcond : (∀ p p', p < κ + s + 1 + (j + 1) * τ → p' < κ + s + 1 + j * τ → IntAt P (M p p')) ∧
        (∀ p p', κ + s + 1 + j * τ ≤ p → p < κ + s + 1 + (j + 1) * τ → p' < κ + s + 1 + j * τ →
          IntAt P (M p p' / (q : E))) ∧
        (∀ p', p' < κ + s + 1 → redP P (M p' p') = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
          (κ + s + 1 ≤ p ∨ symIdx κ S.ρ p' < symIdx κ S.ρ p ∨ (p' = κ + S.ρ ∧ p < κ)) → redP P (M p p') = 0) ∧
        (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
          (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → redP P (M p p') = 0) := by
      refine ⟨fun p p' hp hp' => ?_, fun p p' hp hp' hp'' => h2 p p' hp hp' hp'', h3, h4⟩
      by_cases hpa : p < κ + s + 1 + j * τ
      · exact hint p p' hpa hp'
      · exact intAt_div (h2 p p' (by omega) hp hp') hq
    rw [if_pos hcond, ← hgT, extZ_coe _ _ ⟨g, hgJ⟩, TypeDatum.rho_apply]
    obtain ⟨g₀, D, hg₀, hD, hlam⟩ := GlobalTheory.T.iteratedDepthOneLevel_character_closed_form k _ (Fin τ) S.P S.μ S.tame j ⟨g, hgJ⟩
    rw [hlam]
    simp only [Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val, LocE.lamGvS, map_mul, map_prod, map_inv₀]
    congr 2
    · refine GlobalTheory.T.symmetricLevel_character_at_rational_point E K k P q ι σ₀ ψ₀ χ s κ S hT M (fun p p' hp hp' => hint p p' (by omega) (by omega)) g₀ ?_
      rw [hg₀, hgT]
      ext (x | x) (y | y) <;> rfl
    · rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hdi : ((Matrix.GeneralLinearGroup.det (D i) : kˣ) : k) =
          ι (Matrix.det (Matrix.of fun u v : Fin τ =>
            M (κ + s + 1 + i.val * τ + u.val) (κ + s + 1 + i.val * τ + v.val))) := by
        rw [Matrix.GeneralLinearGroup.val_det_apply, (hD i).2, Ix.diagonalBlockOfMatrix, hgT]
        exact det_of_places ι (Equiv.refl _) (fun u : Fin τ => κ + s + 1 + i.val * τ + u.val) (κ + s + 1 + i.val * τ)
          (fun _ => rfl) M
      refine unit_char hT i _ _ ?_ (valuation_det_of_mem_KO (hD i).1) hdi
      rw [← hC.int, ← hdi, Valuation.mem_integer_iff, valuation_det_of_mem_KO (hD i).1]
    · exact unit_char hT j _ _ (hintdet g hgKO hgT) (valuation_det_of_mem_KO hgKO) (hdet g hgT)
  · rw [extZ_of_not _ _ hJ]
    split_ifs with hc
    · have hnu : ¬ IsUnit (redP P (Matrix.det (Matrix.of fun s' s'' : Fin (κ + s + 1 + j * τ) => M s'.1 s''.1))) := by
        intro hu
        have hint : ∀ p p', p < κ + (s + 1) + j * τ → p' < κ + (s + 1) + j * τ → IntAt P (M p p') :=
          fun p p' hp hp' => hc.1 p p' (by rw [Nat.add_mul]; omega) hp'
        obtain ⟨g, hgKO, hgT⟩ := hKO.2 ⟨hint, hu⟩
        refine hJ ⟨g, (hpat g).2 ⟨hgKO, fun a b hf => ?_⟩, hgT⟩
        rw [hgT]
        exact (hpatM hint).2 ⟨hc.2.2.1, hc.2.2.2⟩ a b hf
      rw [LocE.unitV, dite_eq_right hnu, _root_.inv_zero, mul_zero, map_zero]
    · rw [map_zero]

end GlobalTheory.SymBridge.TopAgree


open GlobalTheory.SymBridge.TopAgree in
theorem GlobalTheory.SymBridge.phiTopAgree_of_tie : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k)
    (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ),
    Comparison₂ P q ι σ₀ ψ₀ χ S → PhiTopAgree P q ι σ₀ ψ₀ χ S := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT τ n' c' n hn' hc' hn e' e he' he x
  subst hc'
  rw [top_entries q ι S τ n' n e' e he' he x,
    core P q ι σ₀ ψ₀ χ S hT τ (s + 1) (n + 0) (by omega)]
  exact congrArg σ₀ (PhiGS_eq q ψ₀ χ κ S.ρ (κ + s + 1) τ (s + 1) 0 n' 0 n x).symm
end
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.formalGroup_height_le_two_good_reduction : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (l : ℂ_[l]))‖ = 1 := by
  first | exact @GlobalTheory.HeightTwo.height_le_two | exact GlobalTheory.HeightTwo.height_le_two | (intros; apply GlobalTheory.HeightTwo.height_le_two <;> assumption)
end
