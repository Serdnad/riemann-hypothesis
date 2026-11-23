module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoHeckeQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle087
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicOfSectionsOfVeryAmple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

open HeckePoint

theorem hasQuot_of_isIsogT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (t' : SAB H S) (ψ : o.t.G ⟶ t'.G) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → IsIsogT o.t t' p ψ → KerSet ψ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  intro E _ _ _ H D l 𝔓 p i S _ s o t' ψ K _ ⟨h𝔓, hco, hp, hp𝔓, hpM⟩ hpr ham hkt hI hker hHk
  obtain ⟨hhom, hfin, het, hsur, hlin, hiso⟩ := hI
  have hG : Out.GlobalFnsSt := (show Out.Laws from GlobalTheory.firstFiveLaws.1).globalFns
  have hab := isAbelianScheme_of_proper o.t o.proper
  have hab' := isAbelianScheme_of_proper t' hpr
  have hW := fun (n : ℤ) (T : Over S) (x y : T ⟶ o.t.G) c c' =>
    weilIs_along_hom hG _ o.t.G t'.G ψ o.t.PP.L t'.PP.L (p ^ 2) n T x y c c' hab hab' o.t.PP.isLB t'.PP.isLB hhom hiso
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  have hMM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hAM : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
  have etaM : ∀ a, o.eta (l.M • a) = 1 := fun a => o.eta_ker _ (by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (natCast_M_mem l) Submodule.mem_top)
  let o' : Ob D l s :=
    { t := t', proper := hpr, ample := ham, ktriv := hkt
      eta := fun a => o.eta (p₀ • a) ≫ ψ
      eta_add := fun a c => by rw [smul_add, o.eta_add, MonObj.mul_comp]
      eta_ker := fun a ha => by rw [o.eta_ker _ (nsmul_mem ha _), MonObj.one_comp]
      etaA := fun a => o.etaA (p₀ • a) ≫ ψ
      etaA_add := fun a c => by rw [smul_add, o.etaA_add, MonObj.mul_comp]
      etaA_ker := fun a => by rw [smul_comm, o.etaA_ker, MonObj.one_comp]
      geom := by
        intro k _ _ x β hx
        obtain ⟨hdet, I, hζ, hA, hM⟩ := o.geom k x β hx
        refine ⟨fun τ => ?_, ?_⟩
        · simp only [← LieEtale.lieMult_iff_of_etale _ _ _ _ ψ o.t.act t'.act hhom het hlin k x τ]
          exact hdet τ
        obtain ⟨C, hC, -, c₂, c₃, c₄, c₅, -⟩ := hHk k x
        have mem : ∀ z : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 ↔ z ∈ C := fun z => (hker k x z).trans (hC z).symm
        let ψx : (Over.mk x ⟶ o.t.G) →* (Over.mk x ⟶ t'.G) :=
          MonoidHom.mk' (fun z => z ≫ ψ) fun a c => MonObj.mul_comp a c ψ
        have uniq : ∀ (n : ℤ) (z w : Over.mk x ⟶ o.t.G) (c c' : kˣ),
            Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c) → Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c') → c = c' :=
          fun n z w c c' h h' => (unitOn_bijective k).1 (CommutatorPairing.weilIs_unique hG hab o.t.PP.isLB h h')
        obtain ⟨I', hζ', hev⟩ := exists_tateIso_heckeQuotient SimAlg.sim_group E H D 𝔓 p k _ _ _
          (fun a g => g ≫ t'.act.act a) _
          (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c)) I ψx h𝔓 hco hp hp𝔓
          (fun y => exists_lift_pt ψ x y)
          (fun a z => by
            show (z ≫ _) ≫ ψ = (z ≫ ψ) ≫ _
            rw [Category.assoc, hlin, Category.assoc])
          (fun J hJ z _ hz' => (mem z).2 (c₂ J hJ hz'))
          (fun z hz => ⟨by
            rw [← comp_act_natCast o.t.act]
            refine c₃ ((mem z).1 hz) _ ?_
            rw [Nat.cast_pow, pow_two]
            refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
            have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp𝔓
            rwa [map_natCast] at this, c₃ ((mem z).1 hz)⟩)
          (fun z w hz hw => by
            have h := c₄ z ((mem z).1 hz) w ((mem w).1 hw)
            rw [← Nat.cast_pow] at h
            exact (congrArg (Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) z w) unitOn_one).mpr h)
          (by rw [← c₅, show ψx.ker = C from Subgroup.ext mem])
          (fun n z w c c' _ _ _ h h' => uniq n z w c c' h h')
          (fun n z w c hn hz hw h => by
            have hlift : ∀ (q : Over.mk x ⟶ t'.G), q ^ n = 1 →
                ∀ a : (Over.mk x).left, ∃ V : (Over.mk x).left.Opens, a ∈ V ∧
                  ∃ θ : Out.ThetaGrp t'.G t'.PP.L n (Out.overRes V), θ.pt = Out.overResι V ≫ q := by
              intro q hq a
              obtain ⟨V, hV, v, hv⟩ := exists_local_gen t'.PP.isLB (K := Fin 2)
                ![(1 : Over.mk x ⟶ t'.G).left, q.left] ![(n : ℤ), -(n : ℤ)] a
              refine ⟨V, hV, ?_⟩
              apply exists_theta t'.cub (by rw [← MonObj.comp_pow, hq, MonObj.comp_one]) v hv
              intro U _ f
              rw [Fin.prod_univ_two, ← MonObj.comp_one (Out.overResι V)]
              rfl
            obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs hG hab' t'.PP.isLB (hlift _ hz) (hlift _ hw)
            obtain ⟨c', rfl⟩ := (unitOn_bijective k).2 c'
            have h₂ := (hW n _ z w 1 _ hc').1
            rw [← Nat.cast_mul] at h₂
            rw [uniq _ z w c c' h h₂]
            exact hc')
        refine ⟨I', by rw [hζ']; exact hζ, fun a => ?_, fun a ha => ?_⟩
        · rw [hev l.A p₀ l.A_pos (hp₀.of_dvd hAM), ← hA, ← Category.assoc]; rfl
        · rw [hev l.M p₀ (by have := l.three_le; omega) (hp₀.of_dvd hMM), ← hM _ (nsmul_mem ha _),
            ← Category.assoc]; rfl }
  refine ⟨o', ψ, ⟨⟨hhom, hfin, het, hsur, hlin, hiso⟩, fun p' hp' a => ?_⟩, hker⟩
  have e := modEq_of_inv hp' hp₀
  exact ⟨congrArg (· ≫ ψ) (eq_of_modEq o.eta o.eta_add etaM (e.of_dvd hMM) a),
    congrArg (· ≫ ψ) (eq_of_modEq o.etaA o.etaA_add o.etaA_ker (e.of_dvd hAM) a)⟩

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyFormulaCompare

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def Same (u : HolUnif A L g) (F : Unif A L g) : Prop :=
  F.exp = u.ex ∧ ∀ i z h, F.fr i z h = u.fr i z

namespace Same

variable {u : HolUnif A L g} {F : Unif A L g} (h : Same u F)
include h

end Same

end Unif

section Analytic

end Analytic

section Principal

theorem tangent_bijective (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) :
    (∀ v, Geo.Tor.IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, Geo.Tor.IsTangent v ∧ u.IsDiff w v := by
  obtain ⟨u₀, H₀, χ₀, E₀, -, -, hv, hw, -⟩ := thetaUnifAV_closed x.P x.rig x.rig_gen
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u₀ hv hw u.ex
    u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u₀ F hF)
  have hd : ∀ w v, u.IsDiff w v ↔ u₀.IsDiff (e w) v :=
    UnifCompare.isDiff_iff u u₀ e.toContinuousLinearEquiv hF
  refine ⟨fun v hv' => ?_, fun w => ?_⟩
  · obtain ⟨w, h1, h2⟩ := hv v hv'
    refine ⟨e.symm w, (hd _ _).2 (by rwa [e.apply_symm_apply]), fun y hy => ?_⟩
    rw [← h2 _ ((hd _ _).1 hy), e.symm_apply_apply]
  · simp only [hd]
    exact hw (e w)

theorem det_ne_zero (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ)
    (hW : ∀ i, u.IsDiff (W i) (x.v i)) : W.det ≠ 0 := by
  obtain ⟨h₁, h₂⟩ := tangent_bijective x u
  refine ((Matrix.isUnit_iff_isUnit_det W).1 (Matrix.vecMul_surjective_iff_isUnit.1 fun w => ?_)).ne_zero
  obtain ⟨v, hv, hd⟩ := (h₂ w).exists
  obtain ⟨c, hc⟩ := (x.basis.2 v hv).exists
  exact ⟨c, (Matrix.vecMul_eq_sum c W).trans ((h₁ v hv).unique
    (UnifDifferential.isDiff_of_isLieComb _ _ _ _ u W x.v c v x.basis.1 hW hc) hd)⟩

end Principal

section Clauses

abbrev RuleIn : Type 1 := ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ

variable (κ : RuleIn)

end Clauses

end GlobalTheory.KeyFormulaCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelInhabitant

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem sum_stdSymp {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) :
    ∑ i, ∑ j, Out.stdSymp g (halves g i) (halves g j) * b j * a i = omegaStd a b := by
  have l : ∀ a, (halves g (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (halves g (.inr a) : ℕ) = g + a := fun _ => rfl
  have ll : ∀ i j, Out.stdSymp g (halves g (.inl i)) (halves g (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l]
    split_ifs <;> omega
  have rr : ∀ i j, Out.stdSymp g (halves g (.inr i)) (halves g (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, r]
    split_ifs <;> omega
  have lr : ∀ i j, Out.stdSymp g (halves g (.inl i)) (halves g (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]
    split_ifs <;> omega
  have rl : ∀ i j, Out.stdSymp g (halves g (.inr i)) (halves g (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]
    split_ifs <;> omega
  simp only [Fintype.sum_sum_type, ll, rr, lr, rl, omegaStd, Finset.sum_sub_distrib]
  simp [sub_eq_add_neg, _root_.mul_comm]

theorem exists_lev_of_rel {k g : ℕ} {G U : Type} [CommGroup G] [CommGroup U] {ze : U}
    (W : G → G → U → Prop) (hW : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹) (v : Fin (2 * g) → G) (hv : ∀ i, v i ^ k = 1)
    (hp : ∀ i j, W (v i) (v j) (ze ^ Out.stdSymp g i j)) :
    ∃ lev : (Fin g ⊕ Fin g → ℤ) → G, (∀ x y, lev (x + y) = lev x * lev y) ∧ (∀ x, lev x ^ k = 1) ∧
      ∀ x y, W (lev x) (lev y) (ze ^ omegaStd x y) := by
  let T : Subgroup G := (powMonoidHom k).ker
  choose w hw hw' using fun x y : T => hW x y x.2 y.2
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (hmul _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (hsymm _ _ _ (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  let e : T →* T →* U := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x))
    fun x x' => MonoidHom.ext fun y => wl x x' y
  let u : Fin g ⊕ Fin g → T := fun i => ⟨v (halves g i), hv _⟩
  have hu : ∀ i j, e (u i) (u j) = ze ^ Out.stdSymp g (halves g i) (halves g j) := fun i j =>
    (hw' (u i) (u j) _ (hp _ _)).symm
  let l : (Fin g ⊕ Fin g → ℤ) → T := fun a => ∏ i, u i ^ a i
  refine ⟨fun a => (l a).1, fun x y => ?_, fun x => (l x).2, fun x y => ?_⟩
  · rw [← Subgroup.coe_mul]
    congr 1
    simp only [l, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  · have : w (l x) (l y) = ze ^ omegaStd x y := by
      show e (l x) (l y) = _
      have z : ∀ {I : Type} [Fintype I] (n : I → ℤ), ze ^ ∑ i, n i = ∏ i, ze ^ n i := fun n =>
        map_prod (zpowersHom U ze) (fun i => Multiplicative.ofAdd (n i)) _
      have s : ∀ i, e.flip (l y) (u i) = ze ^ ∑ j, Out.stdSymp g (halves g i) (halves g j) * y j := fun i => by
        rw [z, MonoidHom.flip_apply]
        simp only [l, map_prod, map_zpow, hu, ← zpow_mul]
      rw [← sum_stdSymp, ← MonoidHom.flip_apply, z]
      show e.flip (l y) (∏ i, u i ^ x i) = _
      simp only [map_prod, map_zpow, s, ← zpow_mul, Finset.sum_mul]
    exact this ▸ hw _ _

end GlobalTheory.SiegelInhabitant

namespace GlobalTheory


open SiegelInhabitant in
theorem exists_principal_siegPre_complex : ∀ (h k : ℕ), 0 < k → ∀ (o : Type) [CommRing o] (em : o →+* ℂ) (ζ : o), IsPrimitiveRoot (em ζ) k → ∃ c : SiegPre h k ζ (spMap em), c.Principal ∧ SmoothOfRelativeDimension h c.A.hom := by
  intro h k hk o _ em ζ hζ
  have hL : Out.Laws := GlobalTheory.T.all_six_abelian_scheme_laws_hold.1
  obtain ⟨P, -, -, hg, -⟩ := polarisedTorus_algebraic h (Complex.I • (1 : Matrix (Fin h) (Fin h) ℂ)) 0 0
    (Matrix.isSymm_one.smul _)
    (by
      have : (Complex.I • (1 : Matrix (Fin h) (Fin h) ℂ)).map Complex.im = 1 := by
        ext i j
        by_cases e : i = j <;> simp [Matrix.one_apply, e]
      rw [this]
      exact Matrix.PosDef.one)
    (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)
  subst hg
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  let ze : ℂˣ := (hζ.isUnit hk.ne').unit
  have hze : IsPrimitiveRoot ze k := IsPrimitiveRoot.coe_units_iff.1 hζ
  have := P.isAb.comm
  obtain ⟨pt, hpt, hw⟩ := EllipticLevel.exists_symplectic_system hL P k hk' ze hze
  obtain ⟨w₁, w₂, -⟩ := hL.weil _ P k (Out.baseOver _)
  obtain ⟨lev, add, tors, weil⟩ := exists_lev_of_rel (G := Out.baseOver _ ⟶ P.A)
    (fun x y c => Out.WeilIs P.A P.L k x y c) w₁ w₂ (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) pt hpt hw
  obtain ⟨c, φ, -, hc, -⟩ := exists_siegPre_of_polAV hL GlobalTheory.T.theorem_of_cube_polAbelianScheme o ℂ em P.g k ζ ze P lev rfl hk' rfl hze add tors
    (fun x y => by
      have e : unitOn (ze ^ omegaStd x y) = unitOn ze ^ omegaStd x y := map_zpow (Units.map _) _ _
      rw [e]
      exact weil x y)
  refine ⟨c, hc, ?_⟩
  have := P.smoothDim
  rw [← Over.w φ.hom]
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map φ.hom))
  have H : SmoothOfRelativeDimension (0 + P.g) (φ.hom.left ≫ P.A.hom) := inferInstance
  rwa [Nat.zero_add] at H

end GlobalTheory
end
