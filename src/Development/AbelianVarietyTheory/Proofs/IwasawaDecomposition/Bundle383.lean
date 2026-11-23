module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

@[reducible] def algK (D : D7) (jE : D.host.E →+* Qb) {M : Fld} (h : KQbar D jE ≤ M) : Algebra D.host.K M :=
  ((IntermediateField.inclusion h).toRingHom.comp (D.host.K.equivMap jE.toRatAlgHom).toRingHom).toAlgebra

theorem nfOf {M : Fld} (h : FiniteDimensional ℚ M) : NumberField M where
  to_finiteDimensional := h

theorem isOfFinOrder_fbar {g : ℕ} [Fact g.Prime] {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) : IsOfFinOrder x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have := IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 : IsOfFinOrder (Units.mk0 y hy) := isOfFinOrder_of_finite _
  exact ((IntermediateField.adjoin (ZMod g) {x}).val.toMonoidHom.comp (Units.coeHom _)).isOfFinOrder h1

section Iota

theorem mem_of_monoidHom {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g : ℕ} [Fact g.Prime]
    (t : Formalism.CyclotomicNorms.Fbar g →* Ω) (x : Formalism.CyclotomicNorms.Fbar g) : t x ∈ B := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
    rcases eq_or_ne (t 0) 0 with h0 | h0
    · rw [h0]; exact zero_mem _
    · rw [(mul_eq_left₀ h0).1 h]; exact one_mem _
  · exact mem_of_pow_eq_one B (isOfFinOrder_fbar hx).orderOf_pos
      (by rw [← map_pow, pow_orderOf_eq_one, map_one])

def redHom {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g l : ℕ} [Fact g.Prime] [Fact l.Prime]
    (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l) (t : Formalism.CyclotomicNorms.Fbar g →* Ω) :
    Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar l where
  toFun x := redThrough B κ (t x)
  map_one' := by rw [map_one]; exact redThrough_one B κ
  map_mul' x y := by
    rw [map_mul]; exact redThrough_mul B κ (mem_of_monoidHom B t x) (mem_of_monoidHom B t y)

end Iota

theorem redHom_inj {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g l : ℕ} [Fact g.Prime] [hl : Fact l.Prime]
    (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l) (t : Formalism.CyclotomicNorms.Fbar g →* Ω)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (x y : Formalism.CyclotomicNorms.Fbar g) (hx : x ≠ 0) (hy : y ≠ 0)
    (cx : (orderOf x).Coprime l) (cy : (orderOf y).Coprime l) (h : redHom B κ t x = redHom B κ t y) : x = y := by
  let ρ : B →+* Formalism.CyclotomicNorms.Fbar l := κ.toRingHom.comp (IsLocalRing.residue B)
  have hρ : ∀ z (hz : z ∈ B), redThrough B κ z = ρ ⟨z, hz⟩ := fun z hz => by
    unfold redThrough; rw [dite_eq_left hz]; rfl
  have hz : x * y⁻¹ ≠ 0 := mul_ne_zero hx (inv_ne_zero hy)
  set n := orderOf (x * y⁻¹) with hn
  have hnpos : 0 < n := (isOfFinOrder_fbar hz).orderOf_pos
  have hcop : n.Coprime l := by
    refine Nat.Coprime.coprime_dvd_left ?_ (Nat.Coprime.mul_left cx cy)
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [mul_pow, inv_pow, pow_mul, pow_orderOf_eq_one, mul_comm (orderOf x), pow_mul, pow_orderOf_eq_one]
    simp
  have hmem := mem_of_monoidHom B t (x * y⁻¹)
  have hprim : IsPrimitiveRoot (t (x * y⁻¹)) n := by
    refine ⟨by rw [← map_pow, hn, pow_orderOf_eq_one, map_one], fun m hm => orderOf_dvd_of_pow_eq_one ?_⟩
    refine ht _ _ (pow_ne_zero _ hz) one_ne_zero ?_
    rw [map_pow, map_one]
    exact hm
  have hprimB : IsPrimitiveRoot (⟨t (x * y⁻¹), hmem⟩ : B) n :=
    IsPrimitiveRoot.coe_submonoidClass_iff.1 hprim
  have hred1 : ρ ⟨t (x * y⁻¹), hmem⟩ = 1 := by
    have hxy : x = x * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
    have hy0 : redHom B κ t y ≠ 0 := by
      intro h0
      have hyo := (isOfFinOrder_fbar hy).orderOf_pos
      have : redHom B κ t y ^ orderOf y = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [h0, zero_pow hyo.ne'] at this
      exact zero_ne_one this
    have h2 : redHom B κ t (x * y⁻¹) * redHom B κ t y = 1 * redHom B κ t y := by
      rw [← map_mul, ← hxy, one_mul, h]
    have h3 := mul_right_cancel₀ hy0 h2
    rw [← hρ]
    exact h3
  have : NeZero ((n : ℕ) : Formalism.CyclotomicNorms.Fbar l) := ⟨fun h0 =>
    (Nat.Prime.coprime_iff_not_dvd hl.out).1 hcop.symm ((CharP.cast_eq_zero_iff _ l n).1 h0)⟩
  have h3 : IsPrimitiveRoot (1 : Formalism.CyclotomicNorms.Fbar l) n := by
    rw [← Polynomial.isRoot_cyclotomic_iff, ← hred1, ← Polynomial.map_cyclotomic n ρ, Polynomial.IsRoot,
      Polynomial.eval_map, Polynomial.eval₂_hom]
    rw [(hprimB.isRoot_cyclotomic hnpos).eq_zero, map_zero]
  have hn1 : n = 1 := IsPrimitiveRoot.one_left_iff.1 h3
  rw [hn, orderOf_eq_one_iff] at hn1
  calc x = x * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
    _ = y := by rw [hn1, one_mul]

end GlobalTheory.ParRay

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.TopA



theorem exists_label_of_eq {g : ℕ} [Fact g.Prime] {t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ} (e : t' = t)
    (h : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (h' : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ)
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t h ζ hζ)) (h1 : Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O) (h2 : LabTwLawO O) :
    ∃ O' : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t' h' ζ hζ), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O' ∧ LabTwLawO O' ∧
      ∀ r f, eSerO O' r f = eSerO O r f := by
  subst e
  exact ⟨O, h1, h2, fun _ _ => rfl⟩




theorem exists_grp_setTy (D : D7) (hE : IsEmpty D.nd.Loc) (X : NTypes D.naut) (h1 h0) (e1 : X.tg = D.ntypes.tg)
    (e2 : X.teichC = D.ntypes.teichC) (e3 : X.eSer = D.ntypes.eSer) (Γ : GrpSide D) :
    ∃ Γ' : GrpSide (setTy D hE X h1 h0), Γ'.ζ = Γ.ζ := by
  have hO := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exists_label_of_eq (congrFun e2 k) (D.ntypes.teichC_inj k) (X.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k) (Γ.O k) (Γ.O_equiv k) (Γ.O_tw k)
  choose O hO1 hO2 hO3 using hO
  refine ⟨{ tA := Γ.tA, tκ := Γ.tκ, teichC_def := fun k => ?_, ζ := Γ.ζ, ζ_gen := Γ.ζ_gen, O := O, eSer_def := fun k f => ?_
            kv := Γ.kv, tg_tame := fun k v => ?_, O_equiv := hO1, O_tw := hO2 }, rfl⟩
  · have := Γ.teichC_def k
    rw [← e2] at this
    exact this
  · exact ((congrFun (congrFun e3 k) f).trans (Γ.eSer_def k f)).trans (hO3 k _ f).symm
  · have := Γ.tg_tame k v
    rw [← e1] at this
    exact this




theorem exists_kv_of_eq (D : D7) {g : ℕ} [Fact g.Prime] {w w' : PlE D.host} (e : w' = w) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (κ : IsLocalRing.ResidueField (D.nd.plOm.1 w) ≃+* Formalism.CyclotomicNorms.Fbar g)
    (h : TameCoupled (D.nd.plOm.1 w) κ σ ζ) :
    ∃ κ' : IsLocalRing.ResidueField (D.nd.plOm.1 w') ≃+* Formalism.CyclotomicNorms.Fbar g, TameCoupled (D.nd.plOm.1 w') κ' σ ζ := by
  subst e
  exact ⟨κ, h⟩


theorem exists_eq_of_heq {P P' : Fin 2 → Type} {β : Type} (e : P' = P) {f : ∀ k, P k → β} {f' : ∀ k, P' k → β} (h : HEq f' f)
    (k : Fin 2) (v : P' k) : ∃ v₀, f k v₀ = f' k v := by
  subst e
  exact ⟨v, by rw [eq_of_heq h]⟩


end GlobalTheory.HeightCounting.TopA

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.CoeffFieldLower

theorem finiteDimensional_muK_one (l : ℕ) [Fact l.Prime] : FiniteDimensional ℚ_[l] (muK l 1) := by
  classical
  have hl : 0 < l ^ 1 := pow_pos (Fact.out : l.Prime).pos 1
  have hfin : ({x : PadicAlgCl l | x ^ (l ^ 1) = 1}).Finite :=
    (nthRoots (l ^ 1) (1 : PadicAlgCl l)).toFinset.finite_toSet.subset fun x hx => by
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hl]; exact hx
  have := hfin.to_subtype
  show FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | x ^ (l ^ 1) = 1})
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x


open Classical in
def bridgeLow (D : D7) (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 D.host.E)) : Loc.FinExt l :=
  if hw : w ∈ placesOver D.host.E l then
    (Classical.choose_spec (GlobalTheory.PlaceBridge.exists_locBridge l D.host.E D.nd.Om w (D.nd.plOm.1 w) hw
      (D.nd.plOm.2 w))).choose
  else ⟨⊥, inferInstance⟩

def low (D : D7) : Big D := fun l hl j =>
  haveI := hl
  ⟨IntermediateField.adjoin ℚ_[l] (Set.range j) ⊔ muK l 1 ⊔
      ⨆ w ∈ (placesOver_finite' D.host.E l (Fact.out : l.Prime).ne_zero).toFinset, (bridgeLow D l w).1, by
    have := GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range j
    have := finiteDimensional_muK_one l
    have : ∀ w, FiniteDimensional ℚ_[l] (bridgeLow D l w).1 := fun w => (bridgeLow D l w).2
    infer_instance⟩

theorem exists_low : ∀ (D : D7), ∃ c0 : Big D, ∀ (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l), (∀ x, j x ∈ (c0 l j).1) ∧ muK l 1 ≤ (c0 l j).1 ∧ ∀ K0 : Loc.FinExt l, (c0 l j).1 ≤ K0.1 → ∀ w ∈ placesOver D.host.E l, ∃ Bw : LocBridge l D.host.E D.nd.Om (_root_.ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(Loc.OL K0), ∀ x, x ∈ D.nd.plOm.1 w ↔ ‖Bw.j x‖ ≤ 1 := by
  intro D
  refine ⟨low D, fun l _ j => ⟨fun x => ?_, ?_, fun K0 hK0 w hw => ?_⟩⟩
  · have h1 : IntermediateField.adjoin ℚ_[l] (Set.range j) ≤ (low D l j).1 := le_sup_left.trans le_sup_left
    exact h1 (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
  · exact le_sup_right.trans le_sup_left
  · have hex := GlobalTheory.PlaceBridge.exists_locBridge l D.host.E D.nd.Om w (D.nd.plOm.1 w) hw (D.nd.plOm.2 w)
    have hspec := (Classical.choose_spec hex).choose_spec
    have hL : (bridgeLow D l w).1 ≤ K0.1 := by
      refine le_trans ?_ hK0
      refine le_trans ?_ le_sup_right
      have hmem : w ∈ (placesOver_finite' D.host.E l (Fact.out : l.Prime).ne_zero).toFinset := by simpa using hw
      exact le_iSup₂ (f := fun w (_ : w ∈ (placesOver_finite' D.host.E l (Fact.out : l.Prime).ne_zero).toFinset) =>
        (bridgeLow D l w).1) w hmem
    have e : bridgeLow D l w = (Classical.choose_spec hex).choose := dif_pos hw
    have hL' : (Classical.choose_spec hex).choose.1 ≤ K0.1 := e ▸ hL
    obtain ⟨Bw, hBj, -⟩ := hspec.2 K0 hL'
    exact ⟨Bw, fun x => by rw [hBj]; exact hspec.1 x⟩

end GlobalTheory.CoeffFieldLower

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Top

def duPre (B : Pre) (u : B.Word) : ℝ :=
  (letI := B.host.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm B.host.E B.R.k) (StandardLattice.stdLat B.host.E B.R.k)) *
    (StandardLattice.idxColLoc (B.host.g 0) B.R.k ^ B.R.f * StandardLattice.idxColLoc (B.host.g 1) B.R.k ^ B.R.f) *
    ∏ τ : Tau B.R, StandardLattice.dimV (fun i : Fin B.R.k => (((B.hcW u τ).u i : ℚ) : ℝ))

def DsPre (B : Pre) : ℝ :=
  (letI := B.host.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm B.host.E B.R.r) (StandardLattice.stdLat B.host.E B.R.r)) *
    (StandardLattice.idxRowLoc (B.host.g 0) B.R.k B.R.m ^ B.R.f * StandardLattice.idxRowLoc (B.host.g 1) B.R.k B.R.m ^ B.R.f) *
    ∏ τ : Tau B.R, Vol.trueDsig B.R (B.hc τ)

theorem Ctx.Over.sizes {K : Ctx} {B : Pre} (h : K.Over B) :
    (∀ u, (B.duStar u : ℝ) = duPre B u) ∧ B.Dstar = DsPre B := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  exact ⟨fun u => K.du_eq u, K.Ds_eq⟩

theorem sigYD_zero (R : Ranks) : 2 ≤ (sigYD R 0).1 ∧ (sigYD R 0).1 + (sigYD R 0).2 = R.r := by
  have h1 := R.two_le_m
  have h2 := R.m_add_three_le_k
  simp only [sigYD, Ranks.rankY, Ranks.r]
  omega

theorem sizes_eq_count (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre) (hv : StandardLattice.VolumeEqMass₂ X.toD7)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    (∀ u, ((X.toD7.mem u).A.duStar : ℝ) = StandardLattice.duStarU X.toD7 u) ∧ X.toD7.what₂.Dstar = StandardLattice.DstarD X.toD7 := by
  obtain ⟨h1, h2⟩ := hO.sizes
  refine ⟨fun u => ?_, ?_⟩
  · have e : (X.toD7.mem u).A.duStar = X.B.duStar u := X.C.A_duStar u
    rw [e]
    refine (h1 u).trans ?_
    unfold duPre StandardLattice.duStarU StandardLattice.duStarP
    congr 1
  · have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
    rw [e, h2]
    have hvol : StandardLattice.volY0 X.toD7 = StandardLattice.massI X.toD7 X.B.R.r := by
      letI := X.toD7.host.cmStar
      have := hv.2 (X.toD7.sp.Y 0) (sigYD X.B.R 0).1 (sigYD X.B.R 0).2 (X.toD7.sp.Y_sig 0)
        (fun τ => X.toD7.Y_sigval 0 (Nat.zero_le _) τ) (sigYD_zero _).1
      rw [(sigYD_zero _).2] at this
      exact this
    unfold DsPre StandardLattice.DstarD StandardLattice.DstarP
    rw [hvol]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

end GlobalTheory.Mem.Top

end
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top Filter

namespace GlobalTheory.Mem.Top.NodeGap

theorem rank_le {s : Scale} {R : Ranks} (h : RankVal s R) (hx : 4 ≤ s.x) : (R.r : ℝ) ≤ s.x ^ 6 := by
  have h1 : (R.k : ℝ) ≤ 2 * s.x ^ (9 / 2 + 10 * s.eps) := h.2.2.1.2
  have h2 : s.x ^ (9 / 2 + 10 * s.eps) ≤ s.x ^ 5 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by have := s.eps_lt; push_cast; linarith)
  have h3 : R.r ≤ 2 * R.k := by have := R.m_add_three_le_k; unfold Ranks.r; omega
  have h4 : (R.r : ℝ) ≤ 2 * R.k := by exact_mod_cast h3
  have h5 : (0 : ℝ) < s.x ^ 5 := by positivity
  calc (R.r : ℝ) ≤ 4 * s.x ^ 5 := by linarith
    _ ≤ s.x * s.x ^ 5 := by gcongr
    _ = s.x ^ 6 := by ring

theorem le_m {s : Scale} {R : Ranks} (h : RankVal s R) {M : ℕ} (hx : (M : ℝ) ^ 4 ≤ s.x) : M ≤ R.m := by
  have h1 : Real.sqrt (s.x * s.delta1) ≤ (R.m : ℝ) := h.2.1.1
  have hx0 : 0 < s.x := by linarith [s.one_lt_alt]
  have h2 : (M : ℝ) ^ 2 ≤ s.x * s.delta1 := by
    have e : s.x * s.delta1 = s.x ^ (1 - s.eps / 8) := by
      unfold Scale.delta1
      rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
    have h3 : s.x ^ ((1 : ℝ) / 2) ≤ s.x ^ (1 - s.eps / 8) :=
      Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by have := s.eps_lt; linarith)
    rw [e]
    refine le_trans ?_ h3
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by rw [← pow_mul]; exact hx)
  have h4 : (M : ℝ) ≤ R.m := (Real.le_sqrt_of_sq_le h2).trans h1
  exact_mod_cast h4

theorem b_eq (K : Ctx) (u : K.P.Word) (τ : Tau K.P.R) :
    ∃ b1 : ℤ, ∀ j : Fin K.P.R.m, (K.P.hcW u τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h0v K.s K.ch : ℚ) ∧
      (K.P.hcW u τ).e j = (K.P.hcW u τ).b j + (h0v K.s K.ch : ℚ) / 2 := by
  obtain ⟨b1, h, -⟩ := (K.ok.hc u).2.2.1
  exact ⟨b1 τ, h τ⟩

theorem eventually_nodeGap_ge_rank_pow (A : ℝ) (N M : ℕ) : Ev fun K => M ≤ K.P.R.m ∧ A * (K.P.R.r : ℝ) ^ N ≤ (h0v K.s K.ch : ℝ) := by
  refine ⟨1, one_pos, fun eps C8 _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨6 * N + 1, fun ch hch =>
    ⟨max (max 4 A) ((M : ℝ) ^ 4), fun K _ _ h3 _ hx => ?_⟩⟩⟩⟩⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx4, hxA⟩, hxM⟩ := hx
  refine ⟨le_m K.ok.rank hxM, ?_⟩
  have h1 := rank_le K.ok.rank hx4
  have h2 : K.s.x ^ (6 * N + 1) ≤ K.s.x ^ K.ch := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le K.s.one_lt_alt.le (by rw [h3]; push_cast; exact hch)
  have h5 : K.s.x ^ K.ch ≤ (⌈K.s.x ^ K.ch⌉₊ : ℝ) := Nat.le_ceil _
  have h6 : (0 : ℝ) ≤ (⌈K.s.x ^ K.ch⌉₊ : ℝ) := Nat.cast_nonneg _
  calc A * (K.P.R.r : ℝ) ^ N ≤ K.s.x * (K.s.x ^ 6) ^ N := by gcongr
    _ = K.s.x ^ (6 * N + 1) := by ring
    _ ≤ (h0v K.s K.ch : ℝ) := by unfold h0v; push_cast; linarith

theorem ev_nodes (A : ℝ) (N M : ℕ) : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → M ≤ X.toD7.R.m ∧
    ∃ h : ℕ, A * (X.toD7.R.r : ℝ) ^ N ≤ (h : ℝ) ∧ ∀ τ, ∃ b1 : ℤ, ∀ j : Fin X.toD7.R.m,
      (X.toD7.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ) ∧ (X.toD7.hc τ).e j = (X.toD7.hc τ).b j + (h : ℚ) / 2 := by
  obtain ⟨a, ha, hp⟩ := eventually_nodeGap_ge_rank_pow A N M
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K0, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K0, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  refine ⟨a3, fun K h1 h2 h3 h4 hx X hO => ?_⟩
  obtain ⟨g1, g2⟩ := ha3 K h1 h2 h3 h4 hx
  have key : ∀ B : Pre, K.Over B → M ≤ B.R.m ∧
      ∃ h : ℕ, A * (B.R.r : ℝ) ^ N ≤ (h : ℝ) ∧ ∀ τ, ∃ b1 : ℤ, ∀ j : Fin B.R.m,
        (B.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ) ∧ (B.hc τ).e j = (B.hc τ).b j + (h : ℚ) / 2 := by
    rintro B ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩
    exact ⟨g1, _, g2, fun τ => b_eq K K.P.u₀ τ⟩
  exact key _ hO

end GlobalTheory.Mem.Top.NodeGap
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top

theorem fc_large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem Ev.mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩

theorem large₂.and {K : Ctx} {p q : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (hp : large₂ K p) (hq : large₂ K q) :
    large₂ K fun B f T => p B f T ∧ q B f T :=
  large₂.inter hp hq

theorem large₂.mono {K : Ctx} {p q : ∀ B : Base, Fr B.toPre → TwDat B → Prop}
    (h : ∀ B f T, K.Over B.toPre → p B f T → q B f T) (hp : large₂ K p) : large₂ K q :=
  large₂.imp hp h

end GlobalTheory.Mem.Top
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.V4.TwoPass

theorem large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem ev_and {p q : Ctx → Prop} (hp : Ev p) (hq : Ev q) : Ev fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 (large_of_sup hL).1
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 (large_of_sup hL).2
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx), hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx)⟩⟩

theorem ev_mono {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  obtain ⟨a, ha, hp⟩ := hp
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun X h1 h2 h3 h4 hx => h X (ha3 X h1 h2 h3 h4 hx)⟩

end GlobalTheory.Mem.Top.V4.TwoPass

namespace GlobalTheory.Mem.Top.V4

open TwoPass

end GlobalTheory.Mem.Top.V4
end
