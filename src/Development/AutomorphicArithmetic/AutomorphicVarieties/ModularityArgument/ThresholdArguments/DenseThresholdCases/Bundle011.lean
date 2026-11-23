module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.EqOnTors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle089
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle086
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle087
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.HeckePolCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle016
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.PtSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle027
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Hi.exists_ordinaryCharacters_heckeAlgebra' :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ), (hset Q R.τ₀).Ax →
    ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (φ : Λ.Λ →ₐ[c.O] T) (gen : (hset Q R.τ₀).Op → T), (∀ i, gen i - algebraMap c.O T (R.a i) ∈ maximalIdeal T) →
    ∀ ψ : ∀ v : V.frame.Vl, Fin n → Dec (F := L) (s.A v.1) →* Tˣ, (∀ v i, Alg.AdicCont (maximalIdeal T) fun g => (ψ v i g : T)) →
    (∀ (v : V.frame.Vl) (i : Fin n) (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)) (y : Uo ((s.w v.1).adicCompletion L)), (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = y →
      (ψ v i g * (hset Q R.τ₀).epsV T v g ^ (i : ℕ) : Tˣ) * φ (R.θ (eV n (hset Q R.τ₀).Sl v i y)) = 1) →
    (∀ (v : V.frame.Vl) (j : Fin n) (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)), (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = unif _ →
      ((∏ i with i ≤ j, ψ v i g * (hset Q R.τ₀).epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
    ∀ v i, r.IsPsi v i (ψ v i) ∧ W.pushCh (φ : Λ.Λ →+* T) (Λ.κ v i) = (ψ v i).comp (V.frame.Iv v).subtype := by
  intro l _ L Ω _ _ _ _ _ _ s n V Q c r ι Λ R hAx T _ _ _ φ gen hgen ψ hc hu hϖ v
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : Finite (ResidueField T) := Finite.of_surjective _ (Alg.resMap_bijective c.O T).2
  have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := hAx.art_spec v
  have hI : ∀ i (g : Dec (F := L) (s.A v.1)) (hg : g ∈ V.frame.Iv v), (ψ v i g : T) = φ (Λ.κ v i ⟨g, hg⟩) := by
    intro i g hg
    have h1 := hu v i (ineIncl (s.hw v.1) ⟨g, hg⟩) g ⟨_, JEx.art_ine _ ha ⟨g, hg⟩⟩ rfl rfl
    have h2 := congrArg (fun z : Λ.Λˣ => φ z) (R.theta v i (ineIncl (s.hw v.1) ⟨g, hg⟩) g hg ⟨_, JEx.art_ine _ ha ⟨g, hg⟩⟩ rfl rfl)
    have h3 : φ ((hset Q R.τ₀).epsV Λ.Λ v g) = (hset Q R.τ₀).epsV T v g := φ.commutes _
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_one, map_one, h3, mul_assoc] at h1 h2
    exact (left_inv_eq_right_inv h1 ((mul_comm _ _).trans h2))
  choose ψ₀ hψ₀ hκ using Λ.inert v
  have hI' : ∀ i (g : Dec (F := L) (s.A v.1)), (g : G L Ω) ∈ Ine (F := L) (s.A v.1) → (ψ v i g : T) = φ (ψ₀ i g) := by
    intro i g hg
    rw [hI i g hg, hκ]
    rfl
  obtain ⟨x, hx⟩ := ha.surj (unif _)
  let p : T →+* ResidueField c.O := Alg.res c.O T
  have hx' : ∀ i, W.pushCh p (ψ v i) (Subgroup.inclusion (Weil_le_Dec _) x) = r.psib v i (Subgroup.inclusion (Weil_le_Dec _) x) := by
    intro i
    refine mul_right_cancel (JEx.eq_of_prod
      (fun i : Fin n => W.pushCh p (ψ v i) (Subgroup.inclusion (Weil_le_Dec _) x) *
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) ^ (i : ℕ))
      (fun i : Fin n => r.psib v i (Subgroup.inclusion (Weil_le_Dec _) x) *
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) ^ (i : ℕ)) (fun j => Units.ext ?_) i)
    have h1 := congrArg p (hϖ v j x (Subgroup.inclusion (Weil_le_Dec _) x) rfl hx)
    have h2 := R.res.unif v j x (Subgroup.inclusion (Weil_le_Dec _) x) rfl hx
    have h3 := (Alg.res_eq_zero_iff c.O T _).2 (hgen (.inr (v, j)))
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h3
    have h4 : p ((hset Q R.τ₀).epsV T v (Subgroup.inclusion (Weil_le_Dec _) x)) =
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) := (Alg.res c.O T).commutes _
    refine Eq.trans ?_ ((h1.trans h3).trans h2.symm)
    simp only [Units.coe_prod, map_prod, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    exact Finset.prod_congr rfl fun k _ => congrArg₂ (· * ·) rfl (congrArg (· ^ (k : ℕ)) h4.symm)
  intro i
  refine ⟨⟨hc v i, fun g => ?_, fun g => ?_⟩, MonoidHom.ext fun g => Units.ext (hI i g.1 g.2).symm⟩
  · have h1 : IsLocallyConstant (W.pushCh p (ψ v i)) :=
      IsLocallyConstant.desc _ Units.val (JEx.res_lc (O := c.O) (hc v i)) Units.val_injective
    let β : Dec (F := L) (s.A v.1) →* (ResidueField c.O)ˣ := r.psib v i
    have h2 : IsLocallyConstant β := JEx.lc_of_open _ (r.psib_open v i)
    have h3 := JEx.char_triv (s.hw v.1) ha (W.pushCh p (ψ v i) / β) (h1.div h2) (fun y hy => by
      rw [MonoidHom.div_apply, div_eq_one]
      refine Units.ext ?_
      exact (congrArg p (hI' i y hy)).trans ((Alg.res_map φ _).trans ((hψ₀ i).red y))) x hx (by rw [MonoidHom.div_apply, div_eq_one]; exact hx' i)
    have h4 : W.pushCh p (ψ v i) g / β g = 1 := DFunLike.congr_fun h3 g
    exact congrArg Units.val (div_eq_one.1 h4)
  · obtain ⟨k, hk⟩ := g.2
    have h1 := JEx.eq_on_tors (s.hw v.1) (ψ v i) (W.pushCh (φ : Λ.Λ →+* T) (ψ₀ i)) (hc v i) (JEx.cont_map φ (hψ₀ i).cont)
      (fun y hy => Units.ext (hI' i y hy)) g.1 (l ^ k) (pow_pos (Fact.out : l.Prime).pos k)
      ((QuotientGroup.eq_one_iff _).1 ((map_pow (QuotientGroup.mk' _) _ _).trans hk))
    exact (congrArg Units.val h1).trans ((congrArg φ ((hψ₀ i).mu g)).trans (φ.commutes _))
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd
namespace UpperTheory.V.Z.Sym.Pl
def LinkedEndEAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N), 1 ≤ e → Even N →
  ∀ (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), l * N ∣ M →
    (∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ η.ker → B'.valuation (M : Ω) < 1) →
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ)
    (k : Pr.GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), B.valuation (l : Ω) < 1 → Φ.Ok C₀ → Φ.Big C₀ →
    Pr.SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L →
    Pr.FinPt c.O Φ 3 ∧ _root_.UpperTheory.V.Pr.AutPtAlt k 3 ι (cycBar L Ω l)⁻¹ ∧ ∃ ka, Sd.IsAlgChar ι ka ∧ _root_.UpperTheory.V.Pr.AutPtAlt k 2 ι ka
end UpperTheory.V.Z.Sym.Pl
end
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem neu_comm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L} {j : GLw n w →* UA L n}
    (hj : ∀ x ∈ locU n w, x = j (cLoc w x)) {g y : UA L n} (hg : cLoc w g = 1) (hy : y ∈ locU n w) : Commute g y := by
  have h1 : (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = 1 := by
    rw [hj _ (GlobalTheory.DefU.LocRet.ret w n g).2]
    have : cLoc w (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = cLoc w g := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl g
    rw [this, hg, map_one]
  have h2 := GlobalTheory.DefU.LocRet.commute_ret g ⟨y, hy⟩
  rwa [h1, inv_one, one_mul] at h2
private theorem ne_J {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {St : Type} [Fintype St] [DecidableEq St]
    {wt : St → Plc L} (hinj : Function.Injective fun u => (wt u).under (𝓞 (Lp L))) (j : ∀ u, GLw n (wt u) →* UA L n)
    (h1 : ∀ u g, j u g ∈ locU n (wt u)) (h2 : ∀ u g, cLoc (wt u) (j u g) = g) (h3 : ∀ u, ∀ x ∈ locU n (wt u), x = j u (cLoc (wt u) x)) :
    ∃ J : GV n wt →* UA L n, (∀ u g, J (Pi.mulSingle u g) = j u g) ∧ (∀ g, J g ∈ GlobalTheory.UnitaryBC.finU (E := L) (n := n)) ∧
      (∀ g u, cLoc (wt u) (J g) = g u) ∧
      (∀ g (v : Plc L), (∀ u, v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L))) → cLoc v (J g) = 1) ∧
      ∀ g k, (∀ u, cLoc (wt u) k = 1) → Commute k (J g) := by
  have h4 : ∀ u g (v : Plc L), v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L)) → cLoc v (j u g) = 1 := fun u g v hv =>
    GlobalTheory.DefU.LocRet.mem_locU_ne (h1 u g) hv
  have hc : Pairwise fun a b => ∀ x y, Commute (j a x) (j b y) := fun a b hab x y =>
    neu_comm (h3 b) (h4 a x _ fun e => hab (hinj e).symm) (h1 b y)
  let J := MonoidHom.noncommPiCoprod j hc
  have hJ : ∀ u g, J (Pi.mulSingle u g) = j u g := fun u g => MonoidHom.noncommPiCoprod_mulSingle j u g
  have key : ∀ P : Subgroup (UA L n), (∀ u g, j u g ∈ P) → ∀ g, J g ∈ P := fun P hP g => by
    have : J.range ≤ P := by
      rw [MonoidHom.noncommPiCoprod_range]
      exact iSup_le fun u => by rintro _ ⟨g, rfl⟩; exact hP u g
    exact this ⟨g, rfl⟩
  refine ⟨J, hJ, key _ fun u g => (h1 u g).1, fun g u => ?_, fun g v hv => key (cLoc v).ker (fun u g => h4 u g v (hv u)) g,
    fun g k hk => ?_⟩
  · have : (cLoc (wt u)).comp J = Pi.evalMonoidHom (fun u => GLw n (wt u)) u := MonoidHom.pi_ext fun i x => by
      rw [MonoidHom.comp_apply, hJ, Pi.evalMonoidHom_apply]
      by_cases h : u = i
      · subst h
        rw [h2, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]
        exact h4 i x _ fun e => h (hinj e)
    exact DFunLike.congr_fun this g
  · exact (Subgroup.mem_centralizer_singleton_iff.1
      (key (Subgroup.centralizer {k}) (fun u g => Subgroup.mem_centralizer_singleton_iff.2
        (neu_comm (h3 u) (hk u) (h1 u g)).symm.eq) g)).symm
private theorem automorphic_tensor_induction_of_local_places {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {n m : ℕ}
    {St : Type} {wt : St → Plc L} {At : St → ValuationSubring Ω} (ht : ∀ u, IsPlaceOver (At u) (wt u))
    (j : ∀ u, GLw n (wt u) →* UA L n) (J : GV n wt →* UA L n)
    (hJ : ∀ u g, J (by classical exact MonoidHom.mulSingle (fun u => GLw n (wt u)) u g) = j u g)
    (τ₀ : KT n wt →* GL (Fin m) ℂ) (χ : ∀ u, Fin n → Ine (F := L) (At u) →* ℂˣ) (hT : _root_.UpperTheory.V.Hi.IsTypeAlt ht τ₀ χ)
    {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) (τ : ∀ u, SmIrr (GLw n (wt u)))
    (hτ : ∀ u, IsoSum ((RU L n).comp (j u)) σ (τ u)) (F : Fin m → UA L n → ℂ) (hF0 : F ≠ 0) (hF1 : ∀ i, F i ∈ σ)
    (hF2 : ∀ (k : KT n wt) i, ∑ a, τ₀ k i a • RU L n (J k) (F a) = F i) :
    ∀ u rc, _root_.UpperTheory.Zero.LLC.IsRecT (ht u) rc → IsTypeWD (ht u) (χ u) (rc (algNorm (τ u))) := by
  haveI : Nontrivial σ := Submodule.nontrivial_iff_ne_bot.2 hσ.ne_bot
  let ρ : Representation ℂ (GV n wt) σ :=
    (⟨σ, fun g v hv => hσ.stable (J g) v hv⟩ : Subrepresentation ((RU L n).comp J)).toRepresentation
  have hρ : ∀ g (y : σ), (ρ g y : UA L n → ℂ) = RU L n (J g) y := fun _ _ => rfl
  refine (hT.2 σ ρ τ fun u => ?_).1 ⟨fun i => ⟨F i, hF1 i⟩, fun h => hF0 (funext fun i => congrArg Subtype.val (congrFun h i)),
    fun k i => Subtype.ext ?_⟩
  · refine UpperTheory.isoSum_of_injective_equivariant_family _ _ _ _ _ ⊤ σ (τ u) Unit (fun _ => σ.subtype) (hτ u) (fun _ _ _ => Submodule.mem_top)
      (fun _ y _ => y.2) (fun _ g y _ => ?_) fun y _ h => Subtype.ext (h ())
    exact (hρ _ y).trans (by rw [hJ]; rfl)
  · change σ.subtype (∑ a, τ₀ k i a • ρ k ⟨F a, hF1 a⟩) = F i

    rw [map_sum, ← hF2 k i]
    rfl
theorem UpperTheory.V.Hi.partUR2Type_alt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ χ : ∀ u : s.St, Fin n → Ine (F := L) (s.A u) →* ℂˣ, _root_.UpperTheory.V.Hi.IsTypeAlt (fun u : s.St => s.hw u) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ →
    ∀ τ : ∀ u : s.St, SmIrr (GLw n (s.w u)), (∀ u : s.St, IsCompAlong σ (locU n (s.w u)) ((cLoc (s.w u)).comp (locU n (s.w u)).subtype) (τ u).ρ) → ∀ (u : s.St) rc, _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc → IsTypeWD (s.hw u) (χ u) (rc (algNorm (τ u))) := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ he σ hσ hY χ hT τ hτ
  letI : DecidableEq s.St := fun a b => Classical.propDecidable _
  obtain ⟨hw, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  choose j h1 h2 _ h3 using fun u : s.St => (secU l L Ω s n hn (wt s u) (hsp _ (by
    rw [hw]
    exact s.split _ (Or.inr (Or.inl u.2))))).1
  obtain ⟨J, hJ, j1, j2, j3, -⟩ := ne_J (wt := wt s)
    (fun a b hab => Subtype.ext ((hw _).symm.trans (hab.trans (hw _)))) j h1 h2 h3
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hFσ⟩ := (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  have f1 := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ he _ fun _ => rfl).1
  have hex : ∃ i ℓ, toForm ι e (F i) ℓ ≠ 0 := by
    by_contra h
    exact hF0 (funext fun i => f1 (F i) (hB.1 i trivial) fun ℓ => by
      by_contra h'
      exact h ⟨i, ℓ, h'⟩)
  obtain ⟨i₀, ℓ, hℓ⟩ := hex
  have j4 : ∀ g (v : Plc L), v.under (𝓞 (Lp L)) ∉ s.St → cLoc v (J g) = 1 := fun g v hv =>
    j3 g v fun a h => hv (by rw [h, hw]; exact a.2)
  refine automorphic_tensor_induction_of_local_places (fun u : s.St => s.hw u) j J (fun u g => ?_) _ χ hT hσ τ
    (fun u => UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ (j u) (h1 u) (h2 u) (h3 u) (τ u) (hτ u)) (fun i => toForm ι e (F i) ℓ)
    (fun h => hℓ (congrFun h i₀)) (fun i => hFσ i ℓ) fun k i => ?_
  · exact hJ u g
  · refine partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ he F hB (J k) (j1 _) (fun v => j4 _ _ ?_) k (fun u => (j2 _ u).symm) ?_
      (fun w hw' => ?_) (fun q => j4 _ _ fun h => Q.notS q (Or.inr (Or.inl h))) i ℓ
    · rw [hw]
      exact fun h => s.St_l _ h v.2
    · rw [j4 _ _ (by rw [hw]; exact s.v0_St)]
      exact one_mem _
    · rw [j4 _ _ fun h => hw' (V.sub (Or.inr (Or.inl h)))]
      exact one_mem _
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Hi.heckeDeterminant_satisfies_deformation_relations_alt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (T : Type) [CommRing T] [Algebra c.O T] (D : W.GDet n T V.frame.G₀) (ψ : ∀ v : V.frame.Vl, Fin n → V.frame.Gv v →* Tˣ) (Gd : (T →ₐ[c.O] Qbar l) → Prop),
    (∀ t : T, (∀ x, Gd x → x t = 0) → t = 0) →
    (∀ x, Gd x → ∃ ρ : V.frame.G₀ →* GL (Fin n) (Qbar l), _root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι lam ρ ∧ D.map x.toRingHom = W.GDet.ofRep (W.mat ρ) ∧ ∀ v, W.HasFlag (ρ.comp (V.frame.φ v)) fun i => W.pushCh x.toRingHom (ψ v i)) →
    (∀ i g, D.lam i (V.frame.star c.O T n (MonoidAlgebra.single g 1)) = D.lam i (MonoidAlgebra.single g 1)) ∧
    (∀ v (g : Fin n → V.frame.Gv v) (h : V.frame.G₀), D.tr (MonoidAlgebra.single h 1 * V.frame.oEl v (ψ v) g) = 0) ∧
    ∀ u, ∀ g ∈ r.Ip u, ∀ h : V.frame.G₀, D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) = 0 := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V c r ι lam T _ _ D ψ Gd hsep hex
  choose ρ hPU hD hfl using hex
  obtain ⟨hP, hO, hI⟩ := JEx.rels V.frame c.O T D ψ (X := {x // Gd x}) (Qbar l) (fun x => x.1) (fun x => ρ x.1 x.2)
    (fun a ha => hsep a fun x hx => ha ⟨x, hx⟩) (fun x => hD x.1 x.2) (fun x => (hPU x.1 x.2).form) (fun x => hfl x.1 x.2)
  refine ⟨(AlgebraTools.Det.polarIffLam _ _ _ _ D).1 hP, fun v g h => AlgebraTools.Det.killsLam D _ (hO v g) _ 1 le_rfl hn,
    fun u g hg h => AlgebraTools.Det.killsLam D _ (hI g fun x => ?_) _ 1 le_rfl hn⟩
  obtain ⟨t, ht, ht1⟩ := JEx.teich c r
  obtain ⟨a, ha⟩ := (hPU x.1 x.2).type t ht u
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  have h1 : a * ρ x.1 x.2 g * a⁻¹ = 1 := by
    refine Units.ext ((ha g hg1).trans ?_)
    have e : ∀ i, t i g = 1 := fun i => ht1 i g (Subgroup.mem_iInf.1 hg2 i)
    simp only [e, Units.val_one, map_one, Matrix.diagonal_one]
  exact conj_eq_one_iff.1 h1
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Hi.heckeDeterminant_reduction_eq_residual_alt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ), (hset Q R.τ₀).Ax →
    ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (gen : (hset Q R.τ₀).Op → T), (∀ i, gen i - algebraMap c.O T (R.a i) ∈ maximalIdeal T) →
    ∀ D : W.GDet n T V.frame.G₀, D.IsCont (maximalIdeal T) →
    (∀ (w : (hset Q R.τ₀).Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
      D.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
    D.map (Alg.res c.O T : T →+* ResidueField c.O) = r.Dbar := by
  intro l _ L Ω _ _ _ _ _ _ s n V Q c r ι Λ R hA T _ _ _ gen hgen D hD hF
  refine JEx.red_eq r D hD _ hA.dense ?_
  rintro g ⟨w, hw, B, σ, hB, hσ, rfl⟩
  have h1 := hF ⟨w, hw⟩ B σ hB hσ
  have h2 := R.res.frob ⟨w, hw⟩ B σ hB hσ
  refine (congrArg (Polynomial.map _) h1).trans (Eq.trans ?_ h2.symm)
  rw [JEx.heckePol_map]
  congr 1
  funext j
  split_ifs with h
  · have h3 := (Alg.res_eq_zero_iff c.O T _).2 (hgen (.inl (⟨w, hw⟩, ⟨j - 1, h.2⟩)))
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h3
    exact h3
  · exact map_one _
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace UpperTheory.V.Hi.LvR
section Gen
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))
end Gen
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V0.frame c.O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))
variable (Q0 : QData V0) (Q : QData V) (hS : V0.S' ⊆ V.S')
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem type_for_r_up_of_type_for (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ht : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt (rUp h) ι τ₀ := by
  intro t' ht'
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  have hk : ∀ i, (p0 h).ker ≤ (t' i).ker := fun i g hg => by
    refine teich_ext _ _ ?_ (ht' i g).2 (one_pow _)
    rw [(ht' i g).1, rUp_chib, MonoidHom.mem_ker.1 hg, map_one]
    simp
  let t : Fin n → V0.frame.G₀ →* c.Oˣ := fun i => (p0 h).liftOfSurjective (surjective_levelChangeBaseGroupHom h) ⟨t' i, hk i⟩
  have e : ∀ i g, t i (p0 h g) = t' i g := fun i g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have := ht t fun i g => by
    obtain ⟨x, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    rw [e, ← rUp_chib]
    exact ht' i x
  have e2 : ∀ (u : s.St) i, (t' i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype) =
      (t i).comp (V0.pr.comp (Ine (F := L) (s.A u)).subtype) := fun u i => MonoidHom.ext fun x =>
    (e i (V.pr x)).symm.trans (congrArg (t i) (levelChangeBaseGroupHom_apply_projection h hp x))
  simp only [e2]
  exact this
end UpperTheory.V.Hi.LvR
end
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi.Up
section Loc
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {w : Plc F} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}
private theorem ord_val (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (ha : IsLocalArtin h a) {lam : Wt F l n} {i : Fin n}
    {ω : (w.adicCompletion F)ˣ →* ℂˣ} {ψ : Dec (F := F) A →* (Qbar l)ˣ} (ho : OrdChar ι a ω (htW lam i) ψ) (s : Weil h) :
    (ψ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) * (cycBar F Ω l s : Qbar l) ^ (i : ℕ) =
      (algPow w (lowW lam i) (a s : w.adicCompletion F))⁻¹ * (ι.symm (ω (a s)) * (((normV w : ℕ) : Qbar l) ^ deg s) ^ (i : ℕ)) := by
  have h1 : (ψ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) = _ := ho.val s _ rfl (Set.mem_univ _)
  have h2 : algPow w (-htW lam i) (a s : w.adicCompletion F) * algPow w (fun _ => 1) (a s : w.adicCompletion F) ^ (i : ℕ) =
      (algPow w (lowW lam i) (a s : w.adicCompletion F))⁻¹ := by
    haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
    haveI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
    unfold algPow
    simp only [finprod_eq_prod_of_fintype]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [zpow_one, ← zpow_natCast, ← zpow_add₀ ((map_ne_zero j.1).2 (a s).ne_zero), ← zpow_neg]
    simp [htW]
  rw [h1, UpperTheory.V.Loc.epsArt hN.aut.art h hw a ha s, ← h2]
  ring
end Loc
section Set
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} {Q : QData V} {c : Coef l} {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r}
  {Λ : LamObj r} (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (x : B.Pt) {lam : Wt L l n}
theorem ordChar_unit_mul_finite_component_eq_one (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hA : (hset Q R.τ₀).Ax) (v : V.frame.Vl) (i : Fin n)
    {ω : ((s.w v.1).adicCompletion L)ˣ →* ℂˣ} (ho : OrdChar ι (artOf (s.hw v.1)) ω (htW lam i) (x.psi v i))
    (u : Uo ((s.w v.1).adicCompletion L)) :
    (ω u : ℂ) * ι ((hset Q R.τ₀).finPart R.θ (x.comp (Λ.toPair B.u)).toRingHom lam v i u) = 1 := by
  have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := hA.art_spec v
  obtain ⟨t, ht⟩ := ha.surj u
  have hd : deg t = 0 := by
    have := ha.ord_eq t
    rw [ht, ord_eq_zero u.2] at this
    omega
  have h1 := congrArg (fun z : Λ.Λˣ => x (Λ.toPair B.u z))
    (R.theta v i t (Subgroup.inclusion (Weil_le_Dec _) t) (deg_eq_zero_iff.1 hd) u rfl ht)
  have h2 := ord_val (w := s.w v.1) hN (hA.Sl_over v) ha ho t
  have h3 := congrArg (fun z : B.Bˣ => x z) (DFunLike.congr_fun (W.LamObj.toPair_spec r Λ B.u v i)
    ⟨Subgroup.inclusion (Weil_le_Dec _) t, deg_eq_zero_iff.1 hd⟩)
  have h4 : x (Λ.toPair B.u ((hset Q R.τ₀).epsV Λ.Λ v (Subgroup.inclusion (Weil_le_Dec _) t) : Λ.Λˣ)) = cycBar L Ω l t :=
    (x.comp (Λ.toPair B.u)).commutes _
  simp only [Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h1
  erw [h4] at h1
  rw [hd, ht, zpow_zero, one_pow, mul_one] at h2
  have h5 := (congrArg (· * _) (h2.symm.trans (congrArg (· * _) h3.symm))).trans h1
  rw [← ι.apply_symm_apply (ω u : ℂ), ← map_mul, ← map_one ι, ← h5]
  congr 1
  change _ * (x (Λ.toPair B.u _) / algPow (s.w v.1) _ _) = _
  rw [div_eq_inv_mul]
  ring
theorem norm_lowVal_inv_mul_psEig_eq_one_and_norm_sub_lt_one (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hA : (hset Q R.τ₀).Ax) (v : V.frame.Vl)
    {ω : Fin n → ((s.w v.1).adicCompletion L)ˣ →* ℂˣ} (ho : ∀ i, OrdChar ι (artOf (s.hw v.1)) (ω i) (htW lam i) (x.psi v i))
    (j : Fin n) : ‖ι.symm (((hset Q R.τ₀).lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1))‖ = 1 ∧
      ‖ι.symm (((hset Q R.τ₀).lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)) - algebraMap c.O (Qbar l) (R.a (.inr (v, j)))‖ < 1 := by
  have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := hA.art_spec v
  obtain ⟨t, ht⟩ := ha.surj (unif _)
  have hd : deg t = -1 := by
    have := ha.ord_eq t
    rw [ht, ord_eq_one GlAx.unif_spec] at this
    omega
  let g : Dec (F := L) (s.A v.1) := Subgroup.inclusion (Weil_le_Dec _) t
  let b : B.Bˣ := ∏ i with i ≤ j, B.u.ψ v i g * (hset Q R.τ₀).epsV B.B v g ^ (i : ℕ)
  have h1 : ι.symm (((hset Q R.τ₀).lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)) = x b := by
    have h4 : x ((hset Q R.τ₀).epsV B.B v g : B.Bˣ) = cycBar L Ω l t := x.commutes _
    have e : (Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1) = Finset.univ.filter fun i : Fin n => i ≤ j :=
      Finset.filter_congr fun i _ => Nat.lt_succ_iff
    simp only [b, HSet.lowVal, psEig, e, Units.coe_prod, map_prod, map_mul, map_inv₀, Units.val_mul, Units.val_pow_eq_pow_val,
      map_pow, h4, RingEquiv.symm_apply_apply, map_natCast]
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h2 := ord_val (w := s.w v.1) hN (hA.Sl_over v) ha (ho i) t
    rw [hd, ht, ← resCard_eq_normV, zpow_neg_one, inv_pow] at h2
    exact h2.symm
  rw [h1]
  refine ⟨pt_unit x b, pt_res x _ _ ?_⟩
  rw [← R.res.unif v j t g rfl ht]
  have h4 : Alg.res c.O B.B ((hset Q R.τ₀).epsV B.B v g : B.Bˣ) = ((hset Q R.τ₀).epsV (ResidueField c.O) v g : (ResidueField c.O)ˣ) :=
    (Alg.res c.O B.B).commutes _
  simp only [b, Units.coe_prod, map_prod, map_mul, Units.val_mul, Units.val_pow_eq_pow_val, map_pow, h4]
  exact Finset.prod_congr rfl fun i _ => congrArg (· * _) ((B.u.psi v i).red g)
end Set
end UpperTheory.V.Hi.Up
end
end
