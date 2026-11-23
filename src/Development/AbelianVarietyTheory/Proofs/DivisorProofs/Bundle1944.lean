module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle408
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
public import Formalism.LocalToGlobal.GlobalTheory.GL3.ProvisionExtensionLink
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareCharUnit

theorem exists_root_of_locIn {D : D7} {K : Type} [Field K] (σ : K →+* ℂ) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E)
    (h : ChrEq c χ) (hL : LocIn σ χ) (x : (AE D)ˣ) (hx : Formalism.L2.Pj.FinUnit x) :
    ∃ ζ : K, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ σ ζ = ((c x : Circle) : ℂ) := by
  have hmem : ((c x : Circle) : ℂ) ∈ σ.fieldRange := by
    obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2 (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ h
    obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
      (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom x)
    rw [hprod x hx.1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
    exact prod_mem fun P _ => hL P _
  obtain ⟨ζ, hζ⟩ := hmem
  obtain ⟨-, -, -, m, hm, hpow⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c h.1.1
  refine ⟨ζ, ⟨m, hm, σ.injective ?_⟩, hζ⟩
  rw [map_pow, map_one, hζ, ← Circle.coe_pow, hpow x hx, Circle.coe_one]

theorem nu_finUnit_root : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    CharsIn G D.what₂.embLL → ∀ (i j : Fin D.R.m) (t : T) (x : (AE D)ˣ), Formalism.L2.Pj.FinUnit x →
    ∃ ζ : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
      D.what₂.embLL ζ = (((Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) /
        (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) x : Circle) : ℂ) := by
  intro D T Lc sc G μ₀ hL hC i j t x hx
  have hi := i.2
  obtain ⟨a, ⟨n₁, h₁, e₁⟩, ha⟩ := exists_root_of_locIn D.what₂.embLL _ _ (hL.mu0 j) (hC.mu0 j) x hx
  obtain ⟨b, ⟨n₂, h₂, e₂⟩, hb⟩ := exists_root_of_locIn D.what₂.embLL _ _ (hL.xi t) (hC.xi t) x hx
  obtain ⟨c, ⟨n₃, h₃, e₃⟩, hc⟩ := exists_root_of_locIn D.what₂.embLL _ _
    (G.ch.chi_eq (D.R.m - i) (by omega) (by omega)) (hC.chi (D.R.m - i) (by omega) (by omega)) x hx
  refine ⟨a * b / c, ⟨n₁ * n₂ * n₃, by positivity, ?_⟩, ?_⟩
  · rw [div_pow, mul_pow]
    have f₁ : a ^ (n₁ * n₂ * n₃) = 1 := by rw [mul_assoc, pow_mul, e₁, one_pow]
    have f₂ : b ^ (n₁ * n₂ * n₃) = 1 := by rw [mul_right_comm, mul_comm, pow_mul, e₂, one_pow]
    have f₃ : c ^ (n₁ * n₂ * n₃) = 1 := by rw [mul_comm, pow_mul, e₃, one_pow]
    rw [f₁, f₂, f₃, one_mul, div_one]
  · rw [mul_div_mul_right_eq_div, map_div₀, map_mul, ha, hb, hc, MonoidHom.div_apply, Circle.coe_div]
    congr 1

end GlobalTheory.SquareCharUnit
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest

namespace GlobalTheory.DepthUnf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def flatProd (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t)
    (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) : ℂ :=
  ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y)

def DepthOK (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (K : ℕ) : Prop :=
  (∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) → flatProd S t Φ β x y ≠ 0 →
        (∀ j : Fin D.R.m, K • x j ∈ pairLat G (.top t j)) ∧ ∀ i : Fin D.R.m, K • y i ∈ pairLat G (.chi i D.R.m)) ∧
  ∀ (x u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) → (∀ j : Fin D.R.m, IsHalf e (u j) ∧ u j ∈ pairLat G (.top t j)) →
      (∀ i : Fin D.R.m, IsHalf e (v i) ∧ v i ∈ pairLat G (.chi i D.R.m)) → flatProd S t Φ β (x + K • u) (y + K • v) = flatProd S t Φ β x y

def ExpWith (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) : Prop :=
  (∀ d ∈ τ.support, (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧
      ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1) ∧
    ∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) →
        (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) = flatProd S t Φ β x y

end GlobalTheory.DepthUnf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid (neg)
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.RallisBottom

variable {D : D7}

def posSig (A : HSp D) : HSp D := { A with sig := fun _ => (A.rank, 0) }

theorem posSig_sigOK {A : HSp D} (h : A.gram = 1) : (posSig A).SigOK := fun τ => by
  have e : (posSig A).gram.map τ = 1 := by
    show A.gram.map τ = 1
    rw [h]; exact Matrix.map_one _ (map_zero τ) (map_one τ)
  show Formalism.UG.HasSignature ((posSig A).gram.map τ) A.rank 0
  rw [e]
  exact GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef Matrix.PosDef.one

theorem thetaFunO_posSig_iff {ψ : AddChar (AF D.host.F) ℂ} {A WW : HSp D} (f : WO (neg A) WW → ℂ) :
    IsThetaFunO ψ (neg (posSig A)) WW f ↔ IsThetaFunO ψ (neg A) WW f :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

theorem isWeil_posSig {ψ : AddChar (AF D.host.F) ℂ} {A WW : HSp D} {χA χW : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep A WW}
    (h : GlobalTheory.Grid.IsWeil ψ true A WW χA χW ω) : GlobalTheory.Grid.IsWeil ψ true (posSig A) WW χA χW ω := by
  unfold GlobalTheory.Grid.IsWeil at h ⊢
  exact
    { std := h.std
      hecS := h.hecS
      hecT := h.hecT
      resS := h.resS
      resT := h.resT
      om_pres := fun p f hf => (thetaFunO_posSig_iff (A := A) (WW := WW) _).2 (h.om_pres p f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf))
      om_heis := fun g k w f hf => h.om_heis g k w f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
      om_aut := fun γ hγ γ' hγ' f hf => h.om_aut γ hγ γ' hγ' f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
      om_cont := fun f hf => h.om_cont f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
      om_unit := fun μ 𝓕 h1 h2 p f hf => h.om_unit μ 𝓕 h1 h2 p f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
      om_split := fun e he g k h1 h2 x y h3 h4 =>
        (h.om_split e he g k h1 h2 x y h3 h4).imp fun _ hr => ⟨hr.1, fun ℓ hℓ f hf =>
          hr.2 ℓ (fun u hu f hf => hℓ u hu f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).2 hf)) f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)⟩ }

theorem isVacO_posSig {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A WW : HSp D} {sA sW LA LW} {f : WO (neg A) WW → ℂ}
    (h : IsVacO ψ θ (neg A) WW sA sW LA LW f) : IsVacO ψ θ (neg (posSig A)) WW sA sW LA LW f :=
  ⟨h.1, ⟨h.2.inf, (thetaFunO_posSig_iff (A := A) (WW := WW) f).2 h.2.theta, h.2.lat, h.2.fock, h.2.norm⟩⟩

variable {T : Type}

def Tri.posSig {A A' WW : HSp D} (X : Tri T A A' WW) : Tri T (posSig A) A' WW :=
  ⟨⟨X.rA.Λ, X.rA.β, X.rA.s, X.rA.B⟩, X.rA', X.rW, X.ω, X.ω', X.vac, X.vac', X.e, X.c, X.f, X.f', X.m, X.fd, X.m', X.fd'⟩

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem isBottomTri_posSig {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) :
    IsBottomTri W i j (Tri.posSig X) := by
  refine ⟨hX.rank, hX.rank', hX.std, hX.std', hX.stdW, ?_⟩
  exact
    { rank := hX.is.rank
      rigA := hX.is.rigA
      rigA' := hX.is.rigA'
      rigW := hX.is.rigW
      weil := fun t => isWeil_posSig (hX.is.weil t)
      weil' := hX.is.weil'
      isVac := isVacO_posSig hX.is.isVac
      isVac' := hX.is.isVac'
      idem := hX.is.idem
      expo := hX.is.expo
      fst := hX.is.fst
      snd := hX.is.snd
      meas := hX.is.meas
      meas' := hX.is.meas' }

theorem sigOK_posSig {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) :
    (posSig A).SigOK := posSig_sigOK hX.std.1

end GlobalTheory.RallisBottom

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.unitaryFinitePart_idempotentBlend_mem_latticeStabilizer : ∀ {D : D7} (V : HSp D) (g : GA D V) (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ ε φ : Lev.EAf D, ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → φ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₁ * β₀⁻¹).val + φ • ((β₀ * β₁⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₀ * β₁⁻¹).val + φ • ((β₁ * β₀⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ := by
  first | exact @GlobalTheory.StabMove.finE_mem_St | exact GlobalTheory.StabMove.finE_mem_St | (intros; apply GlobalTheory.StabMove.finE_mem_St <;> assumption)
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem GlobalTheory.ColNorms.familyVectors : GlobalTheory.ColNorms.FamilyVectors := by
  intro D cc δ B χ _ _ hc hδ hχ _ N N' L L' hA
  obtain ⟨h1, h2⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.vector_bound_link D cc hc δ hδ B χ hχ N N' L L' hA
  refine ⟨h1, h2, ?_⟩
  obtain ⟨χ', e, -, hv, -⟩ := GlobalTheory.TrueTheta.exists_family_of_curve D cc δ ⟨hc, hδ⟩
  obtain ⟨e1, e2, M, hM, hC⟩ := hv N N' L L' hA
  obtain ⟨c, hcE⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ ⟨hc, hδ⟩ N N' _
    (Or.inr ⟨_, _, hA.2.2.1, hA.2.2.2, rfl⟩)).1 _ h1 _ e1 e2
  have hE : B.eNat χ N N' L L' = fun z => c * e N N' L L' z := hcE
  have hQ : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α ∈ Qbar := by
    intro α
    have := GlobalTheory.ThLoc.algTAll D cc δ B χ hc hδ hχ N N' L L' hA 0 ⟨1, one_pos, by simpa using zero_mem _⟩ α
    have hU : U D B.tor 0 (B.eNat χ N N' L L') = B.eNat χ N N' L L' := by
      funext z; simp [U, Hf]
    rwa [hU] at this
  have ht : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α = c * Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α := fun α => by
    rw [hE, GlobalTheory.ProdThetaConj.taylor_const_mul e1.1]
  obtain ⟨α, hα⟩ : ∃ α, Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α ≠ 0 := by
    by_contra h
    push_neg at h
    apply e2
    funext z
    rw [← GlobalTheory.ProdThetaConj.tsum_taylor_mono D e1.1 z]
    simp [h]
  have hMQ : ∀ x ∈ M, x ∈ Qbar := fun x hx => mem_algebraicClosure_iff.2
    (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : M)))
  have hcQ : c ∈ Qbar := by
    have : c = Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α / Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α := by rw [ht, mul_div_cancel_right₀ _ hα]
    rw [this]
    exact div_mem (hQ α) (hMQ _ (hC α))
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {c}) :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.1 hcQ).isIntegral
  refine ⟨M ⊔ IntermediateField.adjoin ℚ {c}, IntermediateField.finiteDimensional_sup _ _, fun β => ?_⟩
  rw [ht]
  exact mul_mem ((le_sup_right : IntermediateField.adjoin ℚ {c} ≤ _) (IntermediateField.subset_adjoin ℚ {c} (Set.mem_singleton _)))
    ((le_sup_left : M ≤ _) (hC β))
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.PsiNontriv

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels WithZero
open scoped nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]

theorem exists_trace_not_int (v : HeightOneSpectrum (𝓞 F)) :
    ∃ z : F, (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1) ∧
      Algebra.trace ℚ F z ∉ (algebraMap ℤ ℚ).range := by
  classical
  set C : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hC
  set N : ℕ := (-(FractionalIdeal.count F v C)).toNat + 1 with hN
  have hP : ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := by simpa using v.ne_bot
  set I : FractionalIdeal (𝓞 F)⁰ F := ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ N)⁻¹ with hI
  have hI0 : I ≠ 0 := inv_ne_zero (pow_ne_zero _ hP)
  have hcount : ∀ w, FractionalIdeal.count F w I = if w = v then -(N : ℤ) else 0 := by
    intro w
    rw [hI, FractionalIdeal.count_inv, FractionalIdeal.count_pow]
    split_ifs with hw
    · subst hw; rw [FractionalIdeal.count_self]; ring
    · rw [FractionalIdeal.count_maximal_coprime F w (Ne.symm hw)]; ring
  have hint : ∀ z ∈ I, ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1 := by
    intro z hz w hw
    have := (GlobalTheory.Idele.mem_iff_valuation_le hI0 z).1 hz w
    rwa [hcount w, if_neg hw, neg_zero, exp_zero] at this
  by_contra H
  push_neg at H
  have hle : I ≤ C := by
    intro x hx
    rw [hC, FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
    intro a ha
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have hxa : x * algebraMap (𝓞 F) F a ∈ I := by
      rw [mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ a hx
    exact H _ (hint _ hxa)
  have := FractionalIdeal.count_mono F v hI0 hle
  rw [hcount v, if_pos rfl] at this
  omega

theorem psiV_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.VacAny.psiV ψ v ≠ 1 := by
  intro F _ _ ψ hψ v h1
  obtain ⟨z, hz, hzt⟩ := exists_trace_not_int (F := F) v
  have hloc : ∀ t : Fv F v, ψ (GlobalTheory.EmbChart.atPlace v t) = 1 := fun t => by
    rw [← GlobalTheory.VacAny.psiV_apply, h1, AddChar.one_apply]
  set zv : Fv F v := algebraMap F (Fv F v) z with hzv
  set α : Af F := algebraMap F (Af F) z - GlobalTheory.AdelicU.singleFin v zv with hα
  have hαint : α ∈ intAf F := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_self]
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = zv := rfl
      rw [this, sub_self]
      exact zero_mem _
    · rw [hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_ne hw, sub_zero]
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = algebraMap F (Fv F w) z := rfl
      rw [this, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap]
      exact hz w hw
  have htr : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * 1) = k := by
    intro a
    have hi : IsIntegral ℤ (Algebra.trace ℚ F ((a : F) * 1)) := by
      rw [mul_one]
      exact Algebra.isIntegral_trace (NumberField.RingOfIntegers.isIntegral_coe a)
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    exact ⟨k, by rw [← hk]; simp⟩
  have h0 := GlobalTheory.LatVacArith.psi_int hψ 1 htr α hαint
  rw [map_one, mul_one] at h0
  have hsplit : pairA F 0 (algebraMap F (Af F) z) = pairA F 0 α + GlobalTheory.EmbChart.atPlace v zv := by
    refine Prod.ext (add_zero (0 : Ainf F)).symm ?_
    show algebraMap F (Af F) z = α + GlobalTheory.AdelicU.singleFin v zv
    rw [hα, sub_add_cancel]
  have hval : ψ (pairA F 0 (algebraMap F (Af F) z)) = 1 := by
    rw [hsplit, AddChar.map_add_eq_mul, h0, hloc, one_mul]
  rw [GlobalTheory.LatVacArith.psi_fin_rat hψ, Complex.exp_eq_one_iff] at hval
  obtain ⟨n, hn⟩ := hval
  apply hzt
  refine ⟨n, ?_⟩
  have hc : ((Algebra.trace ℚ F z : ℚ) : ℂ) = (n : ℂ) := by
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ h2
    rw [hn]; ring
  rw [eq_intCast]
  exact_mod_cast hc.symm

end GlobalTheory.PsiNontriv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.exists_schwartzBruhat_schroedingerFixed_localField : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ], ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  first | exact @GlobalTheory.SchrTestVec.exists_fixed | exact GlobalTheory.SchrTestVec.exists_fixed | (intros; apply GlobalTheory.SchrTestVec.exists_fixed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.schroedinger_mem_schwartzBruhat_finitePlace : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ] (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  first | exact @GlobalTheory.SchrSBFin.schr_mem_SB | exact GlobalTheory.SchrSBFin.schr_mem_SB | (intros; apply GlobalTheory.SchrSBFin.schr_mem_SB <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem _root_.GlobalTheory.T.torus_element_acts_on_frame_columns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E)
    (t : Fin r₀ → ℝ), (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a →
    ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Xf =
        incM F Xf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i))) ∧
      ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Yf =
        incM F Yf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i)⁻¹)) ∧
      ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Yf * J) *ᵥ z = 0 →
        ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ
          (fun i => inclR (F := F) (AF F) (z i)) = fun i => inclR (F := F) (AF F) (z i) := by
  first | exact @GlobalTheory.TorusMat.isTorusElt_mat | exact GlobalTheory.TorusMat.isTorusElt_mat | (intros; apply GlobalTheory.TorusMat.isTorusElt_mat <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.archimedean_mass_product_lower_bound_unitary_pq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) (m : ∀ ρ, Measure (UpqT (p ρ) (q ρ))) (ρ₀ : κ), 1 ≤ r → IsIdent p q Ψ G x σ A e → Continuous π → IsProj p q Ψ G σ A a₀ π → (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) → (∀ ρ, IsMinf (m ρ)) → ∀ S : Set (realSU Ψ G), MeasurableSet S → ENNReal.ofReal ((1 / 16 : ℝ) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S ≤ Measure.pi m (π ⁻¹' S ∩ {b | 0 < (UpqT.mat (b ρ₀)).det.im}) := by
  first | exact @GlobalTheory.CovTop.VolUp.MassLow.massLow | exact GlobalTheory.CovTop.VolUp.MassLow.massLow | (intros; apply GlobalTheory.CovTop.VolUp.MassLow.massLow <;> assumption)
end
