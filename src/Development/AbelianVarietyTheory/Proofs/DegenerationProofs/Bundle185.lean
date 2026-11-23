module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle183
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle175
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle168
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ClosureGroup

theorem exists_rescale {X' S' X S Y T : Scheme.{0}} (π : X' ⟶ S') (e' : S' ⟶ X') (he : e' ≫ π = 𝟙 S')
    (F : X' ⟶ X) (f : S' ⟶ S) (e : S ⟶ X) (hF : e' ≫ F = f ≫ e)
    (F₂ : X' ⟶ Y) (f₂ : S' ⟶ T) (e₂ : T ⟶ Y) (hF₂ : e' ≫ F₂ = f₂ ≫ e₂)
    {L : LB X} {M : LB Y} (hL : L.IsLB) (hM : M.IsLB) (a : LB.Gen (L.pull e)) (ha : a.IsGen)
    (b : LB.Gen (M.pull e₂)) (hb : b.IsGen) (H : LBIso (M.pull F₂) (L.pull F)) :
    ∃ w : LB.Iso (M.pull F₂) (L.pull F), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) (p : L.ι) (q : M.ι),
      F (e' (r z)) ∈ L.U p → F₂ (e' (r z)) ∈ M.U q →
      gm (r ≫ f) z ((L.pull e).U fun _ => p) (a.s fun _ => p) =
        gw w (r ≫ e') z p (fun _ => q) * gm (r ≫ f₂) z ((M.pull e₂).U fun _ => q) (b.s fun _ => q) := by
  obtain ⟨w, hw⟩ := H
  have pg := (isGen_iff w).1 hw
  have m₁ : ∀ (s : S') (p : L.ι), F (e' s) ∈ L.U p → f s ∈ (L.pull e).U fun _ => p := fun s p h =>
    mem_pull.2 ((congrArg (fun k => k s ∈ L.U p) hF).mp h)
  have m₂ : ∀ (s : S') (q : M.ι), F₂ (e' s) ∈ M.U q → f₂ s ∈ (M.pull e₂).U fun _ => q := fun s q h =>
    mem_pull.2 ((congrArg (fun k => k s ∈ M.U q) hF₂).mp h)
  let W : L.ι × M.ι → S'.Opens := fun j =>
    e' ⁻¹ᵁ ((L.pull F).U (fun _ => j.1) ⊓ (M.pull F₂).U (fun _ => j.2))
  have l₁ : ∀ j, W j ≤ f ⁻¹ᵁ (L.pull e).U fun _ => j.1 := fun j s hs => m₁ s _ (mem_pull.1 hs.1)
  have l₂ : ∀ j, W j ≤ f₂ ⁻¹ᵁ (M.pull e₂).U fun _ => j.2 := fun j s hs => m₂ s _ (mem_pull.1 hs.2)
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(S', W j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) j, r z ∈ W j →
      gm r z (W j) (u j) = gm (r ≫ f) z ((L.pull e).U fun _ => j.1) (a.s fun _ => j.1) *
        (gw w (r ≫ e') z j.1 (fun _ => j.2) * gm (r ≫ f₂) z ((M.pull e₂).U fun _ => j.2) (b.s fun _ => j.2))⁻¹ :=
    ⟨fun j => res (l₁ j) (pullU f _ (a.s fun _ => j.1)) *
      ((show Γ(S', W j)ˣ from pullU e' _ (w.s (fun _ => j.1, fun _ => j.2))) * res (l₂ j) (pullU f₂ _ (b.s fun _ => j.2)))⁻¹,
      fun Z r z j hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res r z _ hz _).trans (gm_pull r f z _ (l₁ j hz) _))
        ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          (gm_pull r e' z _ hz _) ((gm_res r z _ hz _).trans (gm_pull r f₂ z _ (l₂ j hz) _)))))))⟩
  obtain ⟨c, hc⟩ := glue_unit ⊤ W (fun _ => le_top) (fun s _ => by
      obtain ⟨p, hp⟩ := exists_chart hL (F (e' s))
      obtain ⟨q, hq⟩ := exists_chart hM (F₂ (e' s))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(p, q), mem_pull.2 hp, mem_pull.2 hq⟩) u (fun i j s hs => by
    have e₁ := gen_trans ha (𝟙 S' ≫ f) s (l₁ i hs.1) (l₁ j hs.2)
    have e₂' := gen_trans hb (𝟙 S' ≫ f₂) s (l₂ i hs.1) (l₂ j hs.2)
    have e₃ := pg _ (𝟙 S' ≫ e') s i.1 j.1 (fun _ => i.2) (fun _ => j.2) (mem_pull.1 hs.1.1) (mem_pull.1 hs.2.1)
      hs.1.2 hs.2.2
    rw [gm_pull_g M F₂ (𝟙 S' ≫ e') s _ _ hs.1.2 hs.2.2] at e₃
    simp only [trF, Fintype.prod_unique, zpow_one, Category.id_comp, ← hF, ← hF₂] at e₁ e₂' e₃
    rw [hu _ _ s i hs.1, hu _ _ s j hs.2]
    simp only [Category.id_comp]
    have alg : ∀ {V : Type} [CommGroup V] (A B x y z x' y' z' : V), x' = A * x → z' = B * z → y' = A * B⁻¹ * y →
        x' * (y' * z')⁻¹ = x * (y * z)⁻¹ := by
      rintro V _ A B x y z _ _ _ rfl rfl rfl
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    exact alg _ _ _ _ _ _ _ _ e₁ e₂' e₃)
  have hv : ∀ (Z : Scheme.{0}) (g : Z ⟶ X') (z : Z) (V : X'.Opens), g z ∈ V →
      gm g z V (res (le_top : V ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c)) = gm (g ≫ π) z ⊤ c := fun Z g z V h =>
    (gm_res g z _ h _).trans (gm_pull g π z ⊤ trivial c)
  let w' : LB.Iso (M.pull F₂) (L.pull F) := ⟨fun j => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s j⟩
  have hw' : ∀ (Z : Scheme.{0}) (g : Z ⟶ X') (z : Z) (p : L.ι) (q), F (g z) ∈ L.U p → g z ∈ (M.pull F₂).U q →
      gw w' g z p q = gm (g ≫ π) z ⊤ c * gw w g z p q := fun Z g z p q hp hq =>
    (map_mul _ _ _).trans (congrArg (· * _) (hv Z g z _ ⟨mem_pull.2 hp, hq⟩))
  refine ⟨w', (isGen_iff w').2 fun Z g z j j' k k' hj hj' hk hk' => ?_, fun Z r z p q hp hq => ?_⟩
  · rw [hw' Z g z j k hj hk, hw' Z g z j' k' hj' hk', pg Z g z j j' k k' hj hj' hk hk', mul_left_comm]
  · have hz : r z ∈ W (p, q) := ⟨mem_pull.2 hp, mem_pull.2 hq⟩
    have e₁ := (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (p, q))).trans (hu Z r z (p, q) hz))
    rw [hw' Z (r ≫ e') z p _ hp (mem_pull.2 hq), Category.assoc, he, Category.comp_id, e₁, _root_.mul_assoc,
      inv_mul_cancel_right]

theorem isSymmetric_of_pull (hG : GlobalFnsSt) {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A]
    [GrpObj A'] [IsCommMonObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hs : Sym A L) (L' : RigLB A') (H : LBIso L'.L (L.pull φ)) : L'.IsSymmetric := by
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG hA hL hs
  obtain ⟨w, hw⟩ := H
  obtain ⟨t, ht⟩ := gen_chartPull (chartPullSame L (K := Fin 2)
    (fun k => (![(GrpObj.inv : A' ⟶ A').left, 𝟙 A'.left] : Fin 2 → _) k ≫ φ) _ ![1, -1] φ fun k => by
      fin_cases k
      · exact PolBaseChange.inv_comm h
      · exact (Category.id_comp _).trans (Category.comp_id _).symm) u hu
  exact GlobalTheory.PrimNorm.isSymmetric_of_hasGen L' (exists_down ((isGen_iff w).1 hw) hL L'.isLB t ht)

theorem isQProjOver_ι {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) (U : X.Opens)
    [QuasiCompact U.ι] : IsQProjOver (U.ι ≫ f) := by
  obtain ⟨N, i, hi, e⟩ := h
  exact ⟨N, U.ι ≫ i, inferInstance, inferInstance, by rw [Category.assoc, e]⟩

theorem valF_eq_mul_of_gm {K : Type} [Field K] {X₁ X₂ X₃ : Scheme.{0}} {x₁ : Sp K ⟶ X₁} {x₂ : Sp K ⟶ X₂}
    {x₃ : Sp K ⟶ X₃} {U₁ : X₁.Opens} {U₂ : X₂.Opens} {U₃ : X₃.Opens} (z : Sp K) (h₁ : x₁ z ∈ U₁) (h₂ : x₂ z ∈ U₂)
    (h₃ : x₃ z ∈ U₃) {u₁ : Γ(X₁, U₁)ˣ} {u₂ : Γ(X₂, U₂)ˣ} {u₃ : Γ(X₃, U₃)ˣ}
    (e : gm x₁ z U₁ u₁ = gm x₂ z U₂ u₂ * gm x₃ z U₃ u₃) :
    valF x₁ U₁ u₁.val = valF x₂ U₂ u₂.val * valF x₃ U₃ u₃.val :=
  (toStk z).injective (by
    rw [map_mul, toStk_valF x₁ U₁ z h₁, toStk_valF x₂ U₂ z h₂, toStk_valF x₃ U₃ z h₃, e, Units.val_mul])

theorem exists_pre : Laws → Laws2 → ThmUSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ex.core.HasTests → ex.core.Indep → ex.core.HasCharts → ex.core.TorsSec (S.r * S.N) → (∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀))) → ∃ Z : ZHPre ρ M U₀, (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) ∧ Z.LocTheta ∧ Nonempty ex.core.Law := by
  intro hL hL2 hU o Ω _ _ _ _ S ρ M U₀ EE Q ex hbig htest hind hch htors ⟨T, hT⟩
  have hcomm : IsCommMonObj ρ.P.A := ρ.P.isAb.comm
  have gp : IsGrpPullback ex.core.A ρ.P.A Q.u₀ (pullback.fst ρ.P.A.hom Q.u₀) := isGrpPullback_pullback ρ.P.A Q.u₀
  obtain ⟨-, hamp, hK⟩ := GlobalTheory.pol_pull _ _ _ _ _ _ _ _ ρ.P.isLB T.L.isLB ρ.P.isAb gp hT
  have hsym : T.L.IsSymmetric := isSymmetric_of_pull hL.globalFns gp ρ.P.isAb ρ.P.isLB ρ.P.sym T.L hT
  have hS := GlobalTheory.SymBaseChange.hypS_baseChange _ _ _ _ _ _ _ _ ρ.P.isLB T.L.isLB gp hT ρ.hypS
  have hN : 4 ≤ S.N := by
    have h2 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    nlinarith
  have hunit : IsUnit ((S.r * S.N : ℕ) : Γ(ex.core.Z, ⊤)) := by
    have h := S.unit.map (M.s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
    rw [map_natCast] at h
    exact h
  have hfew : T.Few (S.r * S.N) := GlobalTheory.ZJ.theta_few hU hL hL2 ex.core T (hamp ρ.P.ample) (hK ρ.P.ktriv) hsym hS S.N _
    hN hunit (hbig.2.2.trans_le (Nat.le_self_pow two_ne_zero _))
  obtain ⟨law, hmain⟩ := GlobalTheory.T.exists_semiAbelian_split_cubical_extension_closure hL ex.core T _ htest hind hch htors hfew
  let _ := law.grp
  let _ := law.comm
  obtain ⟨hsplit, hsemi, PP, cub, m, hF, he, hpull, hsym', hloc, -⟩ := hmain
  have hiso : LBIso T.L.L (PP.L.pull ex.core.a) := by
    obtain ⟨w, hw, -⟩ := hpull
    rw [← hF]
    exact ⟨w, hw⟩
  have e₁ := PolBaseChange.eSec_comm gp
  have e₂ := PolBaseChange.eSec_comm law.pull
  have hs : eSec ex.core.A ≫ ex.core.A.hom = 𝟙 _ := Over.w η[ex.core.A]
  have hsP : eSec ρ.P.A ≫ ρ.P.A.hom = 𝟙 _ := Over.w η[ρ.P.A]
  have hsG : eSec ex.core.GG ≫ ex.core.GG.hom = 𝟙 _ := Over.w η[ex.core.GG]
  obtain ⟨w, hw, hv⟩ := exists_rescale ex.core.A.hom (eSec ex.core.A) hs _ _ _ e₁ _ _ _ e₂ ρ.P.isLB PP.isLB ρ.rig
    ρ.rig_gen PP.rig PP.rigGen (LBIso.trans (pull_isLB PP.isLB _) T.L.isLB (pull_isLB ρ.P.isLB _) hiso.symm hT)
  have hqc : QuasiCompact (Q.G.ι ≫ Q.P.hom) := (GlobalTheory.ZJ.core_basic ex.core).2.2.1
  have hpr := Q.proper
  have hqc' : QuasiCompact Q.G.ι := QuasiCompact.of_comp _ Q.P.hom
  refine ⟨{ u₀ := Q.u₀
            u₀_gen := Q.u₀_pt
            G := ex.core.GG
            grp := law.grp
            comm := law.comm
            semi := hsemi
            dim := law.smooth
            qproj := by
              have h := isQProjOver_ι Q.proj Q.G
              rw [← Category.assoc] at h
              exact h
            φ := ex.a
            cart := law.pull
            L := PP
            cub := cub
            sym := hsym' hsym
            w := w
            w_gen := hw
            w_rig := ?_
            split := hsplit }, ⟨Iso.refl _, Category.id_comp _, rfl, heq_of_eq (Category.comp_id _)⟩, hloc, ⟨law⟩⟩
  intro K _ g x y jP jL hx hy hP hL'
  let r : Sp K ⟶ U₀.toScheme := g ≫ pullback.snd ρ.P.A.hom Q.u₀
  have ry : r ≫ Q.u₀ = y := by
    have h := congrArg (· ≫ ρ.P.A.hom) hy
    simp only [Category.assoc] at h
    rw [pullback.condition] at h
    exact (Category.assoc _ _ _).trans (h.trans ((congrArg (y ≫ ·) hsP).trans (Category.comp_id _)))
  have rx : r ≫ U₀.ι = x := by
    have h := congrArg (· ≫ ex.core.GG.hom) hx
    exact (Category.assoc _ _ _).trans ((congrArg (g ≫ ·) law.pull.1.w.symm).trans ((Category.assoc _ _ _).symm.trans
      (h.trans ((Category.assoc _ _ _).trans ((congrArg (x ≫ ·) hsG).trans (Category.comp_id _))))))
  have rg : r ≫ eSec ex.core.A = g := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ eSec ρ.P.A) ry).trans hy.symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hs).trans (Category.comp_id _))
  let z : Sp K := IsLocalRing.closedPoint K
  have mP : pullback.fst ρ.P.A.hom Q.u₀ (g z) ∈ ρ.P.L.U jP := hP ⟨z, rfl⟩
  have mL : ex.a (g z) ∈ PP.L.U jL := hL' ⟨z, rfl⟩
  have key := hv _ r z jP jL ((congrArg (fun k => pullback.fst ρ.P.A.hom Q.u₀ (k z) ∈ ρ.P.L.U jP) rg).mpr mP)
    ((congrArg (fun k => ex.a (k z) ∈ PP.L.U jL) rg).mpr mL)
  erw [ry, rx, rg] at key
  exact valF_eq_mul_of_gm z (mem_pull.2 ((congrArg (fun k => k z ∈ ρ.P.L.U jP) hy).mp mP))
    (show g z ∈ (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)).U (fun _ => jP) ⊓ (PP.L.pull ex.a).U (fun _ => jL) from
      ⟨mem_pull.2 mP, mem_pull.2 mL⟩) (mem_pull.2 ((congrArg (fun k => k z ∈ PP.L.U jL) hx).mp mL)) key

end GlobalTheory.ClosureGroup
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TestFib

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} {p : ℕ} [Fact p.Prime]

theorem level_ne_zero (S : ThetaSys o Ω) (y : Sp (OO p) ⟶ M.Z) : ((S.r * S.N : ℕ) : kb p) ≠ 0 := by
  have h := S.unit.map (Spec.preimage (rPt p ≫ y ≫ M.s)).hom
  rw [map_natCast] at h
  exact h.ne_zero

variable {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u}

abbrev mb (tm : Q.TMap t c) : Matrix S.J S.J (kb p) :=
  tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)

theorem isUnit_det_mb (tm : Q.TMap t c) : IsUnit (mb tm).det := by
  have h := tm.unit.map ((IsLocalRing.residue (OO p)).comp t.u.j)
  rw [RingHom.map_det] at h
  exact h

theorem crd_image (tm : Q.TMap t c) (x₀ : Sp (kb p) ⟶ t.mod.Φ.G.left) (hx : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _)
    (v : S.J → kb p) (hv : Crd (t.mod.Φ.H 1) t.mod.F x₀ v) :
    (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧
      Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) ((x₀ ≫ t.mod.r) ≫ tm.f) ((mb tm).mulVec v) := by
  have h1 : (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j := by
    rw [Category.assoc, t.mod.cart.1.w, ← Category.assoc, hx]
    exact Category.id_comp _
  refine ⟨h1, tm.crd (kb p) ((IsLocalRing.residue (OO p)).comp t.u.j) _ v (h1.trans ?_)
    (t.mod.red (Over.homMk x₀ hx) v hv)⟩
  exact (Spec.map_comp _ _).symm

theorem image_over (tm : Q.TMap t c) (c' : Sp (kb p) ⟶ t.u.G.left) (h : c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j) :
    (c' ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
  rw [Category.assoc, tm.f_over, ← Category.assoc, h, Category.assoc, c.fac]

theorem mem_cone_iff [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (hB : BaseFacts S M U₀ EE) (tm : Q.TMap t c) (hS : S.Big)
    (v : S.J → kb p) :
    v ∈ cone t.mod.Φ.G.hom (t.mod.Φ.H 1) t.mod.F ↔ (∃ i, t.cls i = 0 ∧ v i ≠ 0) ∧
      ∀ (d : ℕ) (Pf : MvPolynomial S.J (kb p)), d ≤ S.N ^ S.g * S.g.factorial → Pf.IsHomogeneous d →
        (∀ w ∈ Q.Tors (rPt p ≫ y) tm.l, MvPolynomial.eval w Pf = 0) →
        MvPolynomial.eval ((mb tm).mulVec v) Pf = 0 := by
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hsm : SmoothOfRelativeDimension S.g t.mod.Φ.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback t.mod.cart.1 t.mod.smooth
  have hbig : Big S.g S.N (S.r * S.N) := ⟨(GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ t.u).2.2.2.1, hS.1, hS.2.1⟩
  have key := GlobalTheory.T.mem_torusExtensionCone_iff_smallDegreeForms hL.1 hL.2.1 (kb p) t.mod.Φ S.g S.N (S.r * S.N) _ S.J _ t.mod.F t.mod.pol hbig
    t.mod.good t.mod.dim (level_ne_zero S y) hsm
    (fun d hd => (Mod.hilb_special_le_generic p _ _ _ _ _ 0 _ _ _ _ _ _ t.mod d).trans
      (GlobalTheory.T.degreeFormsDimension_genericFibre_le hL o Ω S ρ p y₀ t.u S.J t.σ d hd)) v
  obtain ⟨T₁, T₂⟩ := GlobalTheory.T.torsionPoints_specialFibre_supportCoordinates hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS
  have hinv : ∀ w, (mb tm)⁻¹.mulVec ((mb tm).mulVec w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_mb tm), Matrix.one_mulVec]
  refine key.trans (and_congr (exists_congr fun i => and_congr (map_eq_zero_iff _ t.mod.xe.symm.injective) Iff.rfl)
    ⟨fun H d Pf hd hPf hT => ?_, fun H d Pf hd hPf hT => ?_⟩)
  · obtain ⟨F, hF, hev⟩ := InFibChart.exists_subst (mb tm) hPf
    rw [← hev]
    refine H d F hd hF fun x hx => ?_
    obtain ⟨w, hw, hw'⟩ := T₁ x hx
    exact ⟨w, hw, (hev w).trans (hT _ hw')⟩
  · obtain ⟨F, hF, hev⟩ := InFibChart.exists_subst (mb tm)⁻¹ hPf
    rw [← hinv v, ← hev]
    refine H d F hd hF fun w hw => ?_
    obtain ⟨x, w₀, hx, hw₀, rfl⟩ := T₂ w hw
    obtain ⟨w₁, hw₁, h0⟩ := hT x hx
    obtain ⟨u, hu⟩ := CrdCalc.crd_unique hw₁ hw₀
    rw [hev, hinv, show w₀ = fun j => (u : kb p) * w₁ j from funext hu, InFibChart.eval_scale _ _ hPf, h0, mul_zero]

theorem image_special_fibre_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ x : Sp (kb p) ⟶ Q.P.left, x ≫ Q.P.hom = rPt p ≫ y → ((∃ c' : Sp (kb p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x) ↔ (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS x hx
  constructor
  · rintro ⟨c', hc', rfl⟩
    let x₀ : Sp (kb p) ⟶ t.mod.Φ.G.left := t.mod.cart.1.lift c' (𝟙 _) (hc'.trans (Category.id_comp _).symm)
    have h₁ : x₀ ≫ t.mod.r = c' := t.mod.cart.1.lift_fst _ _ _
    have h₂ : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _ := t.mod.cart.1.lift_snd _ _ _
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists (t.mod.Φ.H_isLB 1) t.mod.F x₀
    have hcr := (crd_image tm x₀ h₂ v hv).2
    rw [h₁] at hcr
    have hov := image_over tm c' hc'
    obtain ⟨k₁, k₂⟩ := (mem_cone_iff hL hB tm hS v).1 ⟨x₀, h₂, hv⟩
    rw [← Category.assoc]
    refine ⟨(GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS _ v hov hcr).2 k₁,
      InFibChart.inFib_of_chart o Ω S ρ M U₀ EE hB Q _ tm.l _ _ hcr ?_⟩
    rw [hov]
    exact k₂
  · rintro ⟨hG, hF⟩
    obtain ⟨x', rfl⟩ : ∃ x' : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme, x' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x := by
      refine ⟨IsOpenImmersion.lift _ x ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      have e : Q.P.hom (x w) = y (rPt p w) :=
        (Scheme.Hom.comp_apply _ _ _).symm.trans
          ((congrArg (fun f : Sp (kb p) ⟶ M.Z => f w) hx).trans (Scheme.Hom.comp_apply _ _ _))
      show Q.P.hom (x w) ∈ Q.W tm.l
      rw [e]
      exact ((IsLocalRing.specializes_closedPoint (rPt p w)).map y.continuous).mem_open (Q.W tm.l).isOpen tm.mem
    have hLB : (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι).IsLB := LB.isLB_pull Q.isLB _
    obtain ⟨w, hw⟩ := CrdCalc.crd_exists hLB (Q.σ tm.l) x'
    obtain ⟨v, rfl⟩ : ∃ v, (mb tm).mulVec v = w := ⟨(mb tm)⁻¹.mulVec w, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_mb tm), Matrix.one_mulVec]⟩
    have hx' : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := (Category.assoc _ _ _).symm.trans hx
    have k₂ := hF tm.l x' _ rfl hw
    rw [hx] at k₂
    obtain ⟨x₀, h₂, hv⟩ := (mem_cone_iff hL hB tm hS v).2
      ⟨(GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS x' v hx' hw).1 hG, k₂⟩
    obtain ⟨h₁, hcr⟩ := crd_image tm x₀ h₂ v hv
    refine ⟨x₀ ≫ t.mod.r, h₁, ?_⟩
    have e : ((x₀ ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ∣_ Q.W tm.l) = x' ≫ (Q.P.hom ∣_ Q.W tm.l) := by
      rw [← cancel_mono (Q.W tm.l).ι, Category.assoc, Category.assoc x', morphismRestrict_ι, hx']
      exact image_over tm _ h₁
    rw [← Category.assoc, ImmSep.eq_of_crd_eq _ _ _ _ _ _ _ hLB (Q.imm tm.l) (kb p) _ x' _
      (by rw [← Category.assoc, e, Category.assoc]) hcr hw]

end GlobalTheory.ZH.TestFib
end
end
