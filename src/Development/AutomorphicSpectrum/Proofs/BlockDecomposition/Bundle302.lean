module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle290
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
import Development.WeilBound.LevelCriteria.IsLevOneIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.HighestDerivProd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle292
public import GroundTheory.AutomorphicForms.InductionParabolicGroups
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle294
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle293
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteNil

theorem thick_J_isNilpotent : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R}
    {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} (T : Thick (nlFun γ p X q κ)), ∀ x ∈ T.J, IsNilpotent x := by
  intro O R _ _ I γ p X q κ T x hx
  by_cases hp : p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have h : x ^ n ∈ T.J ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at h
    exact h
  · obtain ⟨n, hn⟩ : IsNilpotent ((p : ℕ) : T.B) := T.adm.1 hp
    refine ⟨p * n, ?_⟩
    have h1 : x ^ p = (p.factorial : T.B) * T.δ.dpow p x := (T.δ.factorial_mul_dpow_eq_pow hx).symm
    have h2 : (p.factorial : T.B) = (p : T.B) * ((p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, h1, h2, mul_assoc, mul_pow, hn, zero_mul]

end GlobalTheory.CompanionTheory.SiteNil
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickLine

theorem pow_dvd_factorial_mul {p : ℕ} (hp : p.Prime) (N : ℕ) : p ^ N ∣ (p * N).factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, pow_succ]
    exact (mul_dvd_mul ih (Nat.dvd_factorial hp.pos le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem isNilpotent_of_mem {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) {p : ℕ} (hp : p.Prime)
    (hn : IsNilpotent (p : A)) {x : A} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hn
  obtain ⟨k, hk⟩ := pow_dvd_factorial_mul hp N
  refine ⟨p * N, ?_⟩
  rw [← δ.factorial_mul_dpow_eq_pow hx, hk]
  push_cast
  rw [hN]
  simp

theorem ringHom_eq {B C : Type} [CommRing B] [CommRing C] (Q : PDPoly B) {f g : Q.P →+* C}
    (h1 : ∀ b, f (algebraMap B Q.P b) = g (algebraMap B Q.P b)) (h2 : ∀ k, f (Q.e k) = g (Q.e k)) : f = g := by
  ext p
  have hp : p ∈ Submodule.span B (Set.range Q.e) := Q.e.mem_span p
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h2 k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | smul b x _ hx => rw [Algebra.smul_def, map_mul, map_mul, hx, h1]

theorem e_one_mem {B : Type} [CommRing B] (Q : PDPoly B) (J : Ideal B) : Q.e 1 ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem le_comap_ext {B : Type} [CommRing B] (Q : PDPoly B) (J : Ideal B) :
    J ≤ (Q.ext J).comap (algebraMap B Q.P) :=
  fun _ hx => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem s_eq_one (T : Thick (F.cr b ht κ)) : T.s = 1 := by
  have h : (1 : T.B) = T.s * T.i b.t := (Finset.prod_of_isEmpty (ι := Empty) _).symm.trans T.hs
  rw [ht, map_one, mul_one] at h
  exact Units.ext h.symm

variable (T : Thick (F.cr b ht κ)) (Q : PDPoly T.B) (η₀ : DividedPowers (Q.ext T.J)) (hη : Q.IsStd T.δ η₀)
  (hp : b.p ≠ 0)

def line : Thick (F.cr b ht κ) where
  B := Q.P
  i := (algebraMap T.B Q.P).comp T.i
  J := Q.ext T.J
  δ := η₀
  adm := ⟨fun _ => by simpa using (T.adm.1 hp).map (algebraMap T.B Q.P), fun h => absurd h hp⟩
  compat := IsDPMorphism.comp _ hη.dp T.compat
  α := ()
  y := (F.cr b ht κ).Pt.map
    (CommRingCat.ofHom (Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J))) T.y
  inα := trivial
  w r := by
    change Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J)
      ((F.cr b ht κ).str T.y (Ideal.Quotient.mk _ r)) = _
    rw [T.w r]
    rfl
  x j := j.elim
  v j := j.elim
  s := 1
  hx j := j.elim
  hs := (Finset.prod_of_isEmpty (ι := Empty) _).trans (by rw [ht]; simp)
  hv := (map_one _).trans (Finset.prod_of_isEmpty (ι := Empty) _).symm

def toLine : T ⟶ line T Q η₀ hη hp where
  φ := algebraMap T.B Q.P
  u j := j.elim
  comm _ := rfl
  dp := hη.dp
  hle := le_comap_ext Q T.J
  pt := rfl
  hx j := j.elim
  hs := by
    rw [s_eq_one T, map_one, mul_one]
    exact (Finset.prod_of_isEmpty (ι := Empty) _).symm
  hv j := j.elim

variable {T Q η₀ hη hp}

theorem exists_ext {T' : Thick (F.cr b ht κ)} (φ : T ⟶ T') {c : T'.B} (hc : c ∈ T'.J) :
    ∃ ψ : line T Q η₀ hη hp ⟶ T', toLine T Q η₀ hη hp ≫ ψ = φ ∧ ψ.φ (Q.e 1) = c := by
  obtain ⟨G, hG1, hG2⟩ := FubiniStudyChowHeightFormula₂.Adr.Fil.exists_lift Q T'.B φ.φ (fun k => T'.δ.dpow k c) (T'.δ.dpow_zero hc) (fun m k => T'.δ.mul_dpow hc)
  have hGa : G.comp (algebraMap T.B Q.P) = φ.φ := RingHom.ext hG1
  have hGdp : IsDPMorphism η₀ T'.δ G :=
    FubiniStudyChowHeightFormula₂.Adr.dp_of_std T.δ Q η₀ hη T'.δ G c hc (by rw [hGa]; exact φ.dp) hG2
  have hle : Q.ext T.J ≤ T'.J.comap G := Ideal.map_le_iff_le_comap.1 hGdp.1
  refine ⟨{ φ := G, u := fun j => j.elim, comm := fun r => ?_, dp := hGdp, hle := hle, pt := ?_,
            hx := fun j => j.elim, hs := ?_, hv := fun j => j.elim }, ?_, ?_⟩
  · exact (hG1 _).trans (φ.comm r)
  · refine Eq.trans ?_ φ.pt
    have e : CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle) =
        CommRingCat.ofHom (Ideal.quotientMap (Q.ext T.J) (algebraMap T.B Q.P) (le_comap_ext Q T.J)) ≫
          CommRingCat.ofHom (Ideal.quotientMap T'.J G hle) := by
      refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      change Ideal.Quotient.mk T'.J (φ.φ a) = Ideal.Quotient.mk T'.J (G (algebraMap T.B Q.P a))
      rw [hG1]
    rw [e, Functor.map_comp]
    rfl
  · rw [s_eq_one T']
    refine Units.ext ?_
    change (1 : T'.B) = ((∏ j : Empty, (j.elim : T'.Bˣ)) * Units.map G.toMonoidHom 1 : T'.Bˣ)
    simp
  · exact Thick.Hom.ext hGa (funext fun j => j.elim)
  · change G (Q.e 1) = c
    rw [hG2 1]
    exact T'.δ.dpow_one hc

theorem hom_unique {T' : Thick (F.cr b ht κ)} {ψ ψ' : line T Q η₀ hη hp ⟶ T'}
    (h : toLine T Q η₀ hη hp ≫ ψ = toLine T Q η₀ hη hp ≫ ψ') (he : ψ.φ (Q.e 1) = ψ'.φ (Q.e 1)) : ψ = ψ' := by
  refine Thick.Hom.ext (ringHom_eq Q (fun a => ?_) fun k => ?_) (funext fun j => j.elim)
  · exact congrArg (fun f : T ⟶ T' => f.φ a) h
  · have h1 : T'.δ.dpow k (ψ.φ (Q.e 1)) = ψ.φ (η₀.dpow k (Q.e 1)) := ψ.dp.2 (Q.e 1) (e_one_mem Q T.J)
    have h2 : T'.δ.dpow k (ψ'.φ (Q.e 1)) = ψ'.φ (η₀.dpow k (Q.e 1)) := ψ'.dp.2 (Q.e 1) (e_one_mem Q T.J)
    rw [hη.var k] at h1 h2
    have h3 : T'.δ.dpow k (ψ.φ (Q.e 1)) = T'.δ.dpow k (ψ'.φ (Q.e 1)) := congrArg _ he
    exact h1.symm.trans (h3.trans h2)

def lineU (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (hpp : b.p.Prime) :
    (thU (F.cr b ht κ) q hq).U (line T Q η₀ hη hpp.ne_zero) :=
  ⟨(isNilpotent_of_mem η₀ hpp (by simpa using (T.adm.1 hpp.ne_zero).map (algebraMap T.B Q.P))
      (e_one_mem Q T.J)).isUnit_one_add.unit,
    MonoidHom.mem_ker.2 (Units.ext (by
      change Ideal.Quotient.mk (Q.ext T.J) (1 + Q.e 1) = Ideal.Quotient.mk (Q.ext T.J) 1
      exact Ideal.Quotient.eq.2 (by simpa using e_one_mem Q T.J)))⟩

theorem map_lineU {T' : Thick (F.cr b ht κ)} (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (hpp : b.p.Prime)
    (ψ : line T Q η₀ hη hpp.ne_zero ⟶ T') :
    ((((thU (F.cr b ht κ) q hq).map ψ (lineU q hq hpp)).1 : T'.Bˣ) : T'.B) = 1 + ψ.φ (Q.e 1) := by
  change (ψ.φ : Q.P →+* T'.B) ((1 : Q.P) + Q.e 1) = 1 + _
  exact (map_add (ψ.φ : Q.P →+* T'.B) 1 (Q.e 1)).trans (by rw [map_one]; rfl)

theorem main : ∀ {O : Type} [CommRing O] (F : Fn O) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ) (hμ : c μ ∈ b.I) (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (x : b.R), b.p.Prime → (q : b.R) = x ^ b.p → c μ = q - 1 → (∑ i ∈ Finset.range b.p, x ^ i) ∈ b.I → ∀ T : Thick (F.cr b ht κ), ∃ (T₁ : Thick (F.cr b ht κ)) (i : T ⟶ T₁) (η : (thU (F.cr b ht κ) q hq).U T₁), (∀ (T' : Thick (F.cr b ht κ)) (φ : T ⟶ T') (a : (thU (F.cr b ht κ) q hq).U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ (thU (F.cr b ht κ) q hq).map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → (thU (F.cr b ht κ) q hq).map g η = (thU (F.cr b ht κ) q hq).q _ * η → (pdFlt (F.cr b ht κ) c ρ hρ μ hμ).FAcyc i g := by
  intro O _ F b ht κ Λ _ c ρ hρ μ hμ q hq x hpp hqx hcμ hsum T
  have hp0 := hpp.ne_zero
  obtain ⟨Q⟩ : Nonempty (PDPoly T.B) := ⟨GlobalTheory.PDA.Model.pdPoly T.B⟩
  obtain ⟨η₀, hη⟩ := FubiniStudyChowHeightFormula₂.Adr.exists_std T.B T.J T.δ Q
  refine ⟨line T Q η₀ hη hp0, toLine T Q η₀ hη hp0, lineU q hq hpp, ?_, ?_⟩
  · intro T' φ a
    have hc : ((a.1 : T'.Bˣ) : T'.B) - 1 ∈ T'.J := by
      have h : Ideal.Quotient.mk T'.J ((a.1 : T'.Bˣ) : T'.B) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 a.2)
      exact Ideal.Quotient.eq.1 (h.trans (map_one _).symm) |> fun h => by simpa using h
    obtain ⟨ψ, h1, h2⟩ := exists_ext (Q := Q) (η₀ := η₀) (hη := hη) (hp := hp0) φ hc
    refine ⟨ψ, ⟨h1, ?_⟩, ?_⟩
    · refine Subtype.ext (Units.ext ?_)
      refine (map_lineU q hq hpp ψ).trans ?_
      rw [h2]
      ring
    · rintro ψ' ⟨h1', h2'⟩
      have e : 1 + ψ'.φ (Q.e 1) = ((a.1 : T'.Bˣ) : T'.B) := (map_lineU q hq hpp ψ').symm.trans
        (congrArg (fun u : (thU (F.cr b ht κ) q hq).U T' => ((u.1 : T'.Bˣ) : T'.B)) h2')
      refine hom_unique (h1'.trans h1.symm) ?_
      rw [h2]
      exact eq_sub_of_add_eq' e
  · intro g hg hgη
    let gφ : Q.P →+* Q.P := g.φ
    have hgφ : gφ.comp (algebraMap T.B Q.P) = algebraMap T.B Q.P :=
      congrArg (fun f : T ⟶ line T Q η₀ hη hp0 => f.φ) hg
    have hmul : gφ (1 + Q.e 1) = algebraMap T.B Q.P ((T.i x) ^ b.p) * (1 + Q.e 1) := by
      have e : gφ (1 + Q.e 1) = algebraMap T.B Q.P (T.i (q : b.R)) * (1 + Q.e 1) :=
        congrArg (fun u : (thU (F.cr b ht κ) q hq).U (line T Q η₀ hη hp0) =>
          ((u.1 : (line T Q η₀ hη hp0).Bˣ) : (line T Q η₀ hη hp0).B)) hgη
      rw [e, hqx, map_pow]
    have hsum' : (∑ i ∈ Finset.range b.p, (T.i x) ^ i) ∈ T.J := by
      have := T.i_mem hsum

      simpa [map_sum, map_pow] using this
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.CompanionTheory.PDAcyc.main T.δ Q η₀ hη b.p hpp (T.adm.1 hp0) (T.i x) hsum' gφ hgφ g.dp hmul
    have hμ' : ∀ z : Q.P, algebraMap T.B Q.P ((T.i x) ^ b.p - 1) * z =
        algebraMap T.B Q.P (T.i (c μ)) * z := by
      intro z
      rw [hcμ, hqx, map_sub T.i, map_pow, map_one]
    refine ⟨h1, ?_, ?_⟩
    · intro r z hz hz'
      obtain ⟨m, hm, e⟩ := h2 (ρ r) z hz hz'
      exact ⟨m, T.pdPow_anti (hρ.2 r) hm, e.trans (hμ' z)⟩
    · intro r z hz
      obtain ⟨y, hy, e⟩ := h3 (ρ r) z hz
      exact ⟨y, (line T Q η₀ hη hp0).pdPow_anti (hρ.2 r) hy, e.trans (hμ' z)⟩

end GlobalTheory.CompanionTheory.ThickLine
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

section Abstract

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

def IsHK (H : Subgroup G) (E : Set G) : Prop :=
  (∀ h ∈ H, ∀ g, h * g ∈ E ↔ g ∈ E) ∧
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g, ∀ x ∈ K, g * x ∈ E ↔ g ∈ E

theorem IsHK.compl {H : Subgroup G} {E : Set G} (hE : IsHK H E) : IsHK H Eᶜ := by
  obtain ⟨h1, K, hK, h2⟩ := hE
  exact ⟨fun h hh g => not_congr (h1 h hh g), K, hK, fun g x hx => not_congr (h2 g x hx)⟩

theorem IsHK.inter {H : Subgroup G} {E E' : Set G} (hE : IsHK H E) (hE' : IsHK H E') : IsHK H (E ∩ E') := by
  obtain ⟨h1, K, hK, h2⟩ := hE
  obtain ⟨h1', K', hK', h2'⟩ := hE'
  refine ⟨fun h hh g => and_congr (h1 h hh g) (h1' h hh g), K ⊓ K', ?_, fun g x hx =>
    and_congr (h2 g x hx.1) (h2' g x hx.2)⟩
  exact hK.inter hK'

theorem IsHK.union {H : Subgroup G} {E E' : Set G} (hE : IsHK H E) (hE' : IsHK H E') : IsHK H (E ∪ E') := by
  have := (hE.compl.inter hE'.compl).compl
  rwa [Set.compl_inter, compl_compl, compl_compl] at this

theorem IsHK.isOpen {H : Subgroup G} {E : Set G} (hE : IsHK H E) : IsOpen E := by
  obtain ⟨-, K, hK, h2⟩ := hE
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hn : (fun y => g⁻¹ * y) ⁻¹' (K : Set G) ∈ 𝓝 g :=
    (hK.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
  filter_upwards [hn] with y hy
  have e : y = g * (g⁻¹ * y) := by group
  rw [e]
  exact (h2 g _ hy).2 hg

theorem isHK_doubleCoset (H K : Subgroup G) (hK : IsOpen (K : Set G)) (c : G) :
    IsHK H {g | ∃ a ∈ H, ∃ x ∈ K, g = a * c * x} := by
  refine ⟨fun h hh g => ⟨?_, ?_⟩, K, hK, fun g y hy => ⟨?_, ?_⟩⟩
  · rintro ⟨a, ha, x, hx, e⟩
    exact ⟨h⁻¹ * a, mul_mem (inv_mem hh) ha, x, hx, by
      have e2 : g = h⁻¹ * (h * g) := by group
      rw [e2, e]; group⟩
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨h * a, mul_mem hh ha, x, hx, by group⟩
  · rintro ⟨a, ha, x, hx, e⟩
    exact ⟨a, ha, x * y⁻¹, mul_mem hx (inv_mem hy), by
      rw [← mul_assoc, ← e]; group⟩
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, x * y, mul_mem hx hy, by group⟩

def stabSub {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]; simp

theorem cInd_right_inv (H : Subgroup G) (σ : Representation ℂ H W) (f : cIndSpace H σ) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g, ∀ x ∈ K, f.1.1.1 (g * x) = f.1.1.1 g := by
  refine ⟨stabSub (ind H σ) f.1.1, f.1.2, fun g x hx => ?_⟩
  have h : ind H σ x f.1.1 = f.1.1 := hx
  exact congrArg (fun v : indSpace H σ => v.1 g) h

theorem exists_indicator (H : Subgroup G) (σ : Representation ℂ H W) {E : Set G} (hE : IsHK H E)
    (f : cIndSpace H σ) :
    ∃ f' : cIndSpace H σ, (∀ g ∈ E, f'.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → f'.1.1.1 g = 0) := by
  classical
  obtain ⟨h1, K, hK, h2⟩ := hE
  obtain ⟨L, hL, hLi⟩ := cInd_right_inv H σ f
  let b : G → W := fun g => if g ∈ E then f.1.1.1 g else 0
  have hind : b ∈ indSpace H σ := by
    intro h g
    have e : f.1.1.1 ((h : G) * g) = σ h (f.1.1.1 g) := f.1.1.2 h g
    by_cases hg : g ∈ E
    · have hg' : (h : G) * g ∈ E := (h1 h h.2 g).2 hg
      simp only [b, if_pos hg, if_pos hg', e]
    · have hg' : (h : G) * g ∉ E := fun c => hg ((h1 h h.2 g).1 c)
      simp only [b, if_neg hg, if_neg hg', map_zero]
  have hsm : (⟨b, hind⟩ : indSpace H σ) ∈ smoothPart (ind H σ) := by
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H σ) (K ⊓ L) (hK.inter hL) _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show b (g * x) = b g
    by_cases hg : g ∈ E
    · have hg' : g * x ∈ E := (h2 g x hx.1).2 hg
      simp only [b, if_pos hg, if_pos hg', hLi g x hx.2]
    · have hg' : g * x ∉ E := fun c => hg ((h2 g x hx.1).1 c)
      simp only [b, if_neg hg, if_neg hg']
  have hc : (⟨⟨b, hind⟩, hsm⟩ : smoothPart (ind H σ)) ∈ cIndSpace H σ := by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g ?_⟩
    intro h0
    apply hg
    show b g = 0
    by_cases hgE : g ∈ E
    · simp only [b, if_pos hgE]; exact h0
    · simp only [b, if_neg hgE]
  exact ⟨⟨⟨⟨b, hind⟩, hsm⟩, hc⟩, fun g hg => if_pos hg, fun g hg => if_neg hg⟩

theorem exists_cInd_value (H : Subgroup G) (σ : Representation ℂ H W) (hσ : IsSmooth σ)
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (c : G) (w : W) : ∃ e : cIndSpace H σ, e.1.1.1 c = w := by
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 (hσ w)
  have h1O : (1 : G) ∈ O := by
    have : (1 : H) ∈ (Subtype.val ⁻¹' O : Set H) := by rw [hOe]; simp
    exact this
  have hn : (fun x => c * x * c⁻¹) ⁻¹' O ∈ 𝓝 (1 : G) :=
    (hO.preimage (by fun_prop)).mem_nhds (by simpa using h1O)
  obtain ⟨K, hKo, hKc, hKO⟩ := hbase _ hn
  obtain ⟨B, hB, -⟩ := GlobalTheory.CompanionTheory.BZMirOnto.exists_bump H σ K hKo hKc c w (by
    intro a x hx e
    have hax : (a : G) ∈ O := by rw [e]; exact hKO hx
    have : a ∈ (Subtype.val ⁻¹' O : Set H) := hax
    rw [hOe] at this
    exact this)
  refine ⟨B, ?_⟩
  have h := hB 1 1 (one_mem K)
  simpa using h

end Abstract

section Conc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev embedding₂ (n : ℕ) : Mir k n →* Mir k (n + 1) := (levi k (n + 1)).comp (Mir k n).subtype

theorem blockIndex_false_val (m j : ℕ) (a : Fin m) : ((eGP m j ⟨false, a⟩ : Fin (m + j + 1)) : ℕ) = a := by
  simp [eGP, stdSum]

theorem blockIndex_true_val (m j : ℕ) (b : Fin (j + 1)) : ((eGP m j ⟨true, b⟩ : Fin (m + j + 1)) : ℕ) = m + b := by
  simp [eGP, stdSum]

theorem mem_mirabolicParabolic_iff (m j : ℕ) (g : Mir k (m + j)) :
    g ∈ MirabolicParabolic k m j ↔ ∀ (b : Fin (j + 1)) (a : Fin m),
      ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
        (eGP m j ⟨true, b⟩) (eGP m j ⟨false, a⟩) = 0 := by
  show (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j) ↔ _
  rw [mem_parab_iff]
  constructor
  · intro h b a
    exact h true false b a (by decide)
  · intro h x y i l hxy
    cases x <;> cases y <;> first | exact absurd hxy (by decide) | exact h i l

theorem dpow_add (n : ℕ) (s t : ℝ) : dpow (k := k) n (s + t) = dpow n s * dpow n t := by
  ext g
  simp [dpow, Complex.ofReal_add, absPow_add]

theorem isOpen_ker_dpow (n : ℕ) (s : ℝ) :
    IsOpen (((dpow (k := k) n s).ker : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
  IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow (s : ℂ))

end Conc

end GlobalTheory.CompanionTheory.LeibPhi

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.block_index_monotone : ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), Monotone (Zl.JC.blockIdx d hd) := by
  first | exact @GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone | exact GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone | (intros; apply GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.contracting_central_unipotent_congruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ), ValuativeRel.valuation k (t : k) ≤ 1 → ∀ (j : Fin h) (m : ℕ), (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd), leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) * u * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd)) ∧ (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd), (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ * z * leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd)) := by
  first | exact @GlobalTheory.CompanionTheory.ZjContract.zj_contract | exact GlobalTheory.CompanionTheory.ZjContract.zj_contract | (intros; apply GlobalTheory.CompanionTheory.ZjContract.zj_contract <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.gelfand_operator_pairing_adjoint : ∀ (n : ℕ) (w : List (Bool × ℕ)), ∃ (N : ℕ) (c : Fin N → ℂ) (w₁ : Fin N → List (Bool × ℕ)), (∀ χ : Inf n, IsHerm χ → conj (zVal w χ) = ∑ i, c i * zVal (w₁ i) χ) ∧ (LgFacts → RCalc → ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h → ∫ y : G n, ⟪zOp w f y.val, h y.val⟫_ℂ ∂μ = ∑ i, c i * ∫ y : G n, ⟪f y.val, zOp (w₁ i) h y.val⟫_ℂ ∂μ) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.WordAdj.word_adjoint | exact GlobalTheory.CompanionTheory.WaveMult.WordAdj.word_adjoint | (intros; apply GlobalTheory.CompanionTheory.WaveMult.WordAdj.word_adjoint <;> assumption)
end
