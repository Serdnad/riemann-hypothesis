module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle263
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle322
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle304
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle542
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle506
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle344
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowGrpSplit

theorem grpAt_all {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) : GrpAt ch := by
  intro j hj
  have hj' := List.mem_range'_1.1 hj
  obtain ⟨hi, hf, hc, he, hu, hrest⟩ := GlobalTheory.AdelicSplit.adelic_split D (ch.G.V (.grid D.R.m j))
  have hV := ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, by omega⟩ (fun k hk => by
    simp only [Node.grid.injEq] at hk; omega)
  have hlat := congLev_open_compact (ch.G.V (.grid D.R.m j))
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hV.sd) (𝔪 := ⊤) top_ne_bot
  have hR : IsClosed ((rowGrp ch.G j : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) : Set (GA D (ch.G.V (.grid D.R.m j)))) ∧ (∀ a ∈ GinfC _, ∀ b ∈ GfC _, a * b ∈ rowGrp ch.G j → a ∈ rowGrp ch.G j ∧ b ∈ rowGrp ch.G j) ∧
      (∀ μ : Measure (rowGrp ch.G j), μ.IsHaarMeasure → μ.IsInvInvariant) ∧
      ∀ μ : Measure ((rowGrp ch.G j).subgroupOf (GfC _)), μ.IsHaarMeasure → μ.IsInvInvariant := by
    by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · rw [show rowGrp ch.G j = _ from dif_pos h1]
      obtain ⟨a, b, c⟩ := (hrest _ _ _).1
      exact ⟨GlobalTheory.jacGrp_isClosed D _ _ _ _, a, b, c⟩
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      rw [show rowGrp ch.G j = _ from (dif_neg h1).trans (dif_pos h2)]
      obtain ⟨a, b, c⟩ := (hrest _ _ _).2 _ _ _
      exact ⟨GlobalTheory.BesClosed.besGrp_isClosed D _ _ _ _ _ _ _, a, b, c⟩
  exact
    { clA := hi
      clB := hf
      clR := hR.1
      comm := hc
      prod := he
      split := hR.2.1
      le := inf_le_left
      cpt := hlat.2
      opn := by
        have e : (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) :
            Set (GfC (ch.G.V (.grid D.R.m j)))) = Subtype.val ⁻¹'
            (((ch.G.levMax (.grid D.R.m j)).comap (Lev.finE _) : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) :
              Set (GA D (ch.G.V (.grid D.R.m j)))) := by
          ext x
          exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
        rw [e]
        exact hlat.1.preimage continuous_subtype_val
      uniR := hR.2.2.1
      uniRB := hR.2.2.2
      uniB := hu }

theorem grpAt_big : Big fun ch => GrpAt ch :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => grpAt_all ch⟩⟩

end GlobalTheory.RowGrpSplit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColVac

variable {D : D7} {T : Type}

theorem xi_mem_xiVals {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) (x : (AE D)ˣ) :
    Circle.toUnits (L.xi t x) ∈ xiVals L t := by
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have e : L.xi t x = L.xi t (b x) := by
    conv_lhs => rw [hab x, map_mul, GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t) hn0 hn _ (ha x).2, one_mul]
  rw [e]
  have hx := (hb x).1
  generalize b x = u at hx
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 _ _ (hL.xi t)
  let y : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨ι (finPart D (u : AE D)), ι (finPart D ((u⁻¹ : (AE D)ˣ) : AE D)),
      by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one],
      by rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]⟩
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN y
  have h5 := hprod u hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  have h6 : Circle.toUnits (L.xi t u) = ∏ P ∈ S, (L.xiH t).locK P (k P) := by
    apply Units.ext
    rw [Units.coe_prod]
    exact h5
  rw [h6]
  exact prod_mem fun P _ => Subgroup.subset_closure ⟨P, _, rfl⟩

theorem attChr_mu {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) (j n : ℕ) :
    Formalism.IndefR.Lift.attChr (L.mu t j) L.eta n = Formalism.IndefR.Lift.attChr (L.mu μ0 j) L.eta n * L.xi t := by
  have hb : L.xi μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi μ0))
  have e : L.mu t j = L.mu μ0 j * L.xi t := by
    show L.mu0 j * L.xi t = L.mu0 j * L.xi μ0 * L.xi t
    rw [hb, mul_one]
  unfold Formalism.IndefR.Lift.attChr
  rw [e]
  split_ifs
  · exact mul_right_comm _ _ _
  · rfl

section Move

variable {V : HSp D} {k : GA D V} {C Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}



theorem fwd (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (s : Fin V.rank → D.host.E) (hs : s ∈ C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  rw [GlobalTheory.MovedHomLat.bridge]
  exact (h _).1 (Submodule.subset_span ⟨s, hs, rfl⟩)




theorem bwd (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (s : Fin V.rank → D.host.E) (hs : s ∈ Λ) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k⁻¹ *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C := by
  have e2 : (Formalism.IndefR.Lev.finE V k).1 * (Formalism.IndefR.Lev.finE V k⁻¹).1 = 1 :=
    congrArg Units.val (((Formalism.IndefR.Lev.finE V).map_mul k k⁻¹).symm.trans
      ((congrArg (Formalism.IndefR.Lev.finE V) (mul_inv_cancel k)).trans (Formalism.IndefR.Lev.finE V).map_one))
  rw [GlobalTheory.MovedHomLat.bridge]
  refine (h _).2 ?_
  rw [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨s, hs, rfl⟩

end Move

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {N : Std G U}

theorem isVac_moved (Z : Normal W N) (t : T) {j : ℕ} (hj : j < D.R.m) :
    W.IsVac (.top t j) (W.om (.top t j) ((N.u (.top j)).1, (N.u (.top (j + 1))).1) (Z.vac (.top t j))) := by
  have h0 := N.u_lat (.top j) hj.le
  have h1 := N.u_lat (.top (j + 1)) hj
  have H := GlobalTheory.MovedHomLat.actO_latO_onto (G.V (.top j)) (G.V (.top (j + 1))) (N.u (.top j)).1 (N.u (.top (j + 1))).1
    _ _ _ _ (fwd h0) (fwd h1) (bwd h0) (bwd h1)
  refine GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)) W.θ_is
    _ _ _ _ _ _ _ _ _ _ (fun τ => ?_) (fun τ => ?_) (fun u => ⟨fun hu => ?_, ?_⟩) _ (Z.vac_is (.top t j) hj)
  · rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC W.θ τ _ (N.u (.top j)).2, Matrix.mul_one, Matrix.one_mul]
  · rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC W.θ τ _ (N.u (.top (j + 1))).2, Matrix.mul_one, Matrix.one_mul]
  · obtain ⟨w, hw, e⟩ := H.2 u hu
    exact ⟨w, hw, e.symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact H.1 w hw

theorem colVac : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∃ v, IsColVac ch v ∧ ∃ (κ : ℕ → ℂˣ) (z : T → ℕ → ℂˣ), (∀ t j, z t j ∈ xiVals R.toLevCh t) ∧ ∀ (t : T) (j : ℕ), j < D.R.m → ch.W.om (.top t j) (ch.G.toPair (.top t j) (ch.S.N.u (Pair.top t j : Pair T).small).1 (ch.S.N.u (Pair.top t j : Pair T).big).1) (ch.S.Z.vac (.top t j)) = ((κ j * z t j : ℂˣ) : ℂ) • v j := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch _
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  choose x hx using fun j => GlobalTheory.RecDict.exists_isDetRoot D (ch.G.V (.top j)) (ch.S.N.u (.top j)).1
  refine ⟨fun j => ch.W.om (.top A.μ0 j) ((ch.S.N.u (.top j)).1, (ch.S.N.u (.top (j + 1))).1) (ch.S.Z.vac (.top A.μ0 j)),
    fun t j hj => isVac_moved ch.S.Z A.μ0 hj, fun _ => 1,
    fun t j => Circle.toUnits (R.toLevCh.xi t ((x j)⁻¹ * x (j + 1))),
    fun t j => xi_mem_xiVals hL t _, fun t j hj => ?_⟩
  have hW0 := ch.W.om_is (.top A.μ0 j) (show j + 1 ≤ D.R.m from hj)
  have hWt := ch.W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)
  have eS : ch.G.chrS (.top t j) = ch.G.chrS (.top A.μ0 j) * R.toLevCh.xi t := attChr_mu hL t _ _
  have eT : ch.G.chrT (.top t j) = ch.G.chrT (.top A.μ0 j) * R.toLevCh.xi t := attChr_mu hL t _ _
  rw [eS, eT] at hWt
  have e := GlobalTheory.TupRoot.twist_eq hW0 hWt (hx j) (hx (j + 1)) (ch.S.Z.vac_is (.top A.μ0 j) hj).2.theta
  rw [(ch.S.Z.free t A.μ0 j).2.1]
  refine e.trans ?_
  congr 1
  rw [one_mul, ← MonoidHom.map_inv, ← MonoidHom.map_mul]
  rfl

end GlobalTheory.ColVac

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CombsExist

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum



theorem exists_comb_model {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D)
    (Φ : WO S T → ℂ) (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (he : e * e = e)
    (hec : e * cA D e = 0) (hinf : infPart D e = 0)
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ) :
    ∃ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0 ∧ IsHalf (e + cA D e) u) ∧ ∀ f₀ Tm,
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
        (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm →
      comb ψ S T c f₀ = Tm Φ := by
  classical
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hce : cA D e * e = 0 := by rw [mul_comm, hec]
  have half1 : ∀ u : WO S T, IsHalf e u → IsHalf (e + cA D e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have half2 : ∀ u : WO S T, IsHalf (cA D e) u → IsHalf (e + cA D e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S T ψ
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin' Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    refine ⟨ψ (symplOH S T x y) • Finsupp.single (x + y) 1, fun u hu => ?_, fun f₀ Tm hTm => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset (Finsupp.support_smul hu))]
      have h1 := infPart_of_half hinf ((isHalf_iff S T).2 hx)
      have h2 := infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy)
      refine ⟨?_, fun i j => ?_⟩
      · ext i j
        have a1 := congrFun (congrFun h1 i) j
        have a2 := congrFun (congrFun h2 i) j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at a1 a2 ⊢
        rw [RingHom.map_add (f := _), a1, a2, add_zero]
      · rw [Matrix.add_apply, mul_add, half1 x ((isHalf_iff S T).2 hx) i j, half2 y ((isHalf_iff S T).2 hy) i j]
    have s0 := GlobalTheory.isSBHalf_halfInd e (latO S T ΛS ΛT fun _ => True)
    have s1 : IsSBHalf e (latO S T ΛS ΛT fun _ => True)
        fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e (latO S T ΛS ΛT fun _ => True) (t + (k * k') • u) =
            halfInd e (latO S T ΛS ΛT fun _ => True) t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := hTm.vac
    rw [one_smul] at v1
    rw [e1, hTm.trans _ s1 x ((isHalf_iff S T).2 hx), hTm.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    have hxy := heisL_heisL S T ψ x y f₀
    change heisO ψ S T x (heisO ψ S T y f₀) = ψ (symplOH S T x y) • heisO ψ S T (x + y) f₀ at hxy
    rw [hxy, GlobalTheory.LocComb.comb_smul, GlobalTheory.LocComb.comb_single]
  | zero => exact ⟨0, by simp, fun f₀ Tm _ => by rw [LinearMap.map_zero]; simp [comb]⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨c, h1, h2⟩ := hg
    obtain ⟨c', h1', h2'⟩ := hg'
    exact ⟨c + c', fun w hw => (Finset.mem_union.1 (Finsupp.support_add hw)).elim (h1 w) (h1' w), fun f₀ Tm h => by
      rw [LinearMap.map_add (f := _), GlobalTheory.LocComb.comb_add, h2 f₀ Tm h, h2' f₀ Tm h]⟩
  | smul a g _ hg =>
    obtain ⟨c, h1, h2⟩ := hg
    exact ⟨a • c, fun w hw => h1 w (Finsupp.support_smul hw), fun f₀ Tm h => by
      rw [LinearMap.map_smul, GlobalTheory.LocComb.comb_smul, h2 f₀ Tm h]⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T}

theorem exists_isCombOf {p : Pair T} (hS : IsSelfDualC (G.pS p) (G.latS p)) (hT : IsSelfDualC (G.pT p) (G.latT p))
    (d : FinDatum G t p) : ∃ c, IsCombOf W d c := by
  obtain ⟨c, h1, h2⟩ := exists_comb_model W.ψ _ _ _ _ d.e d.fn W.ψ_std hS hT (idemSum_mul_self d.e_is) d.e_is.2
    (infPart_idemSum d.e_is) d.sb
  exact ⟨c, fun u hu => (h1 u hu).1, fun u hu => (h1 u hu).2, fun f₀ hth hvac =>
    ⟨(GlobalTheory.PlaceModelSum.placeModelExistsSum D W.ψ W.ψ_std _ _ _ _ hS hT d.P d.e d.e_is f₀ hth hvac).1, h2 f₀⟩⟩

theorem exists_isCombs {μ₀ : T} (hL : L.Is μ₀) (τ : PureDat G t →₀ ℂ) : ∃ c, IsCombs W τ c := by
  have sdT : ∀ j, j ≤ D.R.m → IsSelfDualC (G.V (.top j)) (G.Λ (.top j)) := fun j hj =>
    (G.isV (X := .top j) hj fun _ h => by cases h).sd
  have sdG : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i D.R.m)) (G.Λ (.grid i D.R.m)) := fun i hi => by
    cases i with
    | zero => exact (colY_isV D T L μ₀ hL D.R.m le_rfl).sd
    | succ i => exact (G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ fun _ h => by cases h).sd
  choose c₁ h₁ using fun (d : PureDat G t) (j : Fin D.R.m) =>
    exists_isCombOf W (p := .top t j) (sdT j j.2.le) (sdT (j + 1) j.2) (d.1 j)
  choose c₂ h₂ using fun (d : PureDat G t) (i : Fin D.R.m) =>
    exists_isCombOf W (p := .chi i D.R.m) (isSelfDualC_neg (sdG (i + 1) i.2)) (sdG i i.2.le) (d.2 i)
  refine ⟨fun d => (fun j => if h : j < D.R.m then c₁ d ⟨j, h⟩ else 0, c₂ d), fun d _ => ⟨fun j => ?_, h₂ d⟩⟩
  dsimp only
  rw [dite_eq_left j.2]
  exact h₁ d j

theorem combs_exist : Big fun ch => ∀ t Φ β τ, ch.S.IsExpansion t Φ β τ → ∃ c, IsCombs ch.W τ c :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ _ _ _ τ _ => exists_isCombs ch.W s.core.lev τ⟩⟩

end GlobalTheory.CombsExist

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowCover

theorem mem_GfC_of_hasLoc : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → x ∈ GfC _ := by
  intro D T L sc G t B j hj x g hx
  obtain ⟨e, ⟨⟨es, hes, rfl⟩, -⟩, hg, -⟩ := hx
  have h0 : infPart D ((∑ PP ∈ locPl G t, es PP) + cA D (∑ PP ∈ locPl G t, es PP)) = 0 := by

    rw [map_sum (cA D), ← Finset.sum_add_distrib, map_sum]
    refine Finset.sum_eq_zero fun PP hPP => ?_
    obtain ⟨-, -, v, ε, ⟨α, rfl, -⟩, h⟩ := (hes PP hPP).1
    rw [h]; exact TensorProduct.zero_tmul _ _
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := congrArg (infPart D) (hg i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at this
  refine Eq.trans this ?_
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end GlobalTheory.RowCover
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

theorem pureTensor_oppArgs_local : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) (w : Pl D.host.E) (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid G t w).rank b.tgt)) (Fin ((locGrid G t w).rank b.src)) (Kw w) → ℂ) (x : ∀ i : Fin D.R.m, Mx D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank) (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank), (locGrid G t w).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ (oppArgs t B w x y) = (∏ i : Fin D.R.m, φ (.ex i D.R.m) (B.coord t w (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ ((x i).map fun a => cpt w (toEAf D a)))) * ∏ j : Fin D.R.m, φ (.theta D.R.m j) (B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ ((y j).map fun a => cpt w (toEAf D a))) := by
  intro D T L sc G t B w φ x y
  show ((GlobalTheory.SplitFlip.oppositePath D.R.m).map fun b => φ b (oppArgs t B w x y b)).prod = _
  simp only [GlobalTheory.SplitFlip.oppositePath, List.map_append, List.prod_append, List.map_reverse,
    List.prod_reverse, List.map_map]
  rw [← List.map_coe_finRange_eq_range, List.map_map, List.map_map, ← Fin.prod_univ_def, ← Fin.prod_univ_def]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_ <;> simp [oppArgs]

theorem flipFin_local_identity : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (Φ : ch.G.Datum) (e : AE D) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → (∀ x y, (∀ i, IsHalf e (x i)) → (∀ j, IsHalf e (y j)) → (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y)) → ∀ (n : locPl ch.G t → ℕ) (xw : ∀ w : locPl ch.G t, Fin (n w) → ℂ) (φw : ∀ w : locPl ch.G t, Fin (n w) → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ (w : locPl ch.G t) z, Tflip ch.W ch.S.B t Φ w.1 z = ∑ i, xw w i * (locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φw w i) z) → ∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ Fintype.piFinset (fun w => (Finset.univ : Finset (Fin (n w)))), (∏ w, xw w (a w)) * (∏ i : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (x i)) * ∏ j : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (y j) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch t Φ e τ φ hloc hfac n xw φw hexp x y
  by_cases hh : (∀ i, IsHalf e (x i)) ∧ ∀ j, IsHalf e (y j)
  · rw [hfac x y hh.1 hh.2, ← Finset.prod_coe_sort]
    simp_rw [hexp, pureTensor_oppArgs_local]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hh.1, hh.2, ↓reduceIte, Finset.prod_mul_distrib]
    rw [mul_assoc]
    congr 2 <;> exact Finset.prod_comm
  · rw [not_and_or] at hh
    rcases hh with hh | hh <;> simp only [not_forall] at hh <;> obtain ⟨k, hk⟩ := hh
    · trans (0 : ℂ)
      · rw [Finsupp.sum]
        refine Finset.sum_eq_zero fun d hd => ?_
        have h0 : (φ d).1 k (x k) = 0 := by
          by_contra hne
          exact hk (((hloc d hd).1 k).1.1 (x k) hne)
        apply mul_eq_zero_of_left
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) h0
      · symm
        refine Finset.sum_eq_zero fun a _ => ?_
        apply mul_eq_zero_of_left
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by dsimp only; exact if_neg hk)
    · trans (0 : ℂ)
      · rw [Finsupp.sum]
        refine Finset.sum_eq_zero fun d hd => ?_
        have h0 : (φ d).2 k (y k) = 0 := by
          by_contra hne
          exact hk (((hloc d hd).2 k).1.1 (y k) hne)
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) h0
      · symm
        refine Finset.sum_eq_zero fun a _ => ?_
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by dsimp only; exact if_neg hk)

end GlobalTheory.LocAsm
end
