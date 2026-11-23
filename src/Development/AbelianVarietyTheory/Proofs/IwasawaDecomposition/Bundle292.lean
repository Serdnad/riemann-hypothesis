module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle263
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle281
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle272
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle039
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Mathlib.GroupTheory.Transfer
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PowEqPowIffModEqOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem read_updS_keep (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (err : type_of% R.err0)
    (hX : ∀ b, (((R.updS R.kap lam).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) :
    ∃ (Y' : Read (A3 := A3) ((R.updS R.kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS R.kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  refine ⟨reFaceRead (R.updS R.kap lam) F Dc Sp Zsc err X0 Y,
    reFaceReadL (R.updS R.kap lam) F Dc Sp Zsc err X0 Y (scalReadL R F lam hX X0 Y Z), ?_⟩
  have fields := And.intro (Eq.refl Y.tup) <| And.intro (Eq.refl Y.tupT) <|
    And.intro (HEq.refl Y.jA) <| And.intro (HEq.refl Y.jA0) <|
    And.intro (HEq.refl Y.eMt) <| And.intro (HEq.refl Y.PY) <|
    And.intro (HEq.refl Y.eFT) <| And.intro (HEq.refl Y.IL) <|
    And.intro (HEq.refl Y.PW) <| And.intro (HEq.refl Y.eE) <|
    And.intro (HEq.refl Y.mj.eW) <| And.intro (HEq.refl Z.eRR) (HEq.refl Z.jW)
  -- Compare the fully elaborated conjunction in the kernel, which reduces the copied fields.
  run_tac
    Lean.Elab.Tactic.closeMainGoalUsing `exact fun target _ => do
      let proof ← Lean.Elab.Tactic.elabTerm (Lean.mkIdent `fields) none
      let actual ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      let target ← Lean.instantiateMVars target
      let context ← Lean.instantiateLCtxMVars (← Lean.getLCtx)
      match Lean.Kernel.isDefEq (← Lean.getEnv) context actual target with
      | .ok true => pure proof
      | .ok false => throwError "The copied fields are not definitionally equal"
      | .error err => Lean.throwKernelException err

end GlobalTheory.Mem.R3

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.Lift

def sgnGL (n : ℕ) (S : Type) [CommRing S] (ε : ℤˣ) : GL (Fin n) S := Units.map (Int.castRingHom _).toMonoidHom ε

theorem sgnGL_val (n : ℕ) (S : Type) [CommRing S] (ε : ℤˣ) : (sgnGL n S ε).1 = (ε : ℤ) • 1 := (zsmul_one _).symm

theorem sgnGL_comm {n : ℕ} {S : Type} [CommRing S] (ε : ℤˣ) (x : GL (Fin n) S) : x * sgnGL n S ε = sgnGL n S ε * x :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, sgnGL_val, mul_smul_comm, smul_mul_assoc, mul_one, one_mul])

theorem bc_sgnGL {n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (ε : ℤˣ) :
    Formalism.UG.bc f (sgnGL n S ε) = sgnGL n S' ε :=
  Units.ext (map_intCast (f.mapMatrix : Matrix (Fin n) (Fin n) S →+* Matrix (Fin n) (Fin n) S') (ε : ℤ))

theorem map_sgn {n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (ε : ℤˣ) (i j : Fin n) :
    (sgnGL n S' ε).1 i j = f ((sgnGL n S ε).1 i j) := by
  rw [← bc_sgnGL f]; rfl

theorem frGL_sgn {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (ε : ℤˣ) : frGL β (sgnGL n _ ε) = sgnGL n _ ε := by
  have h : intGL F E n (sgnGL n _ ε) = sgnGL n _ ε := bc_sgnGL (Formalism.L2.Herm.intAf F E).subtype ε
  rw [frGL, MonoidHom.comp_apply, h, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, sgnGL_comm, mul_inv_cancel_right]

theorem exists_matrix_sign {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) (ε : ℤˣ)
    (h : ∀ P ∈ T, redFn β P x = sgnGL n _ ε) {b : 𝓞 E} (hb : b ∈ J)
    {K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) • (K - (sgnGL n _ ε).1) = M • N :=
  GlobalTheory.LevelUnique.exists_matrix_hat hfr T hJ hx ⟨sgnGL n _ ε, rfl⟩
    (fun P hP => by rw [h P hP, redFn_frGL, bc_sgnGL]) hb hK
    (fun i j => by
      rw [frGL_sgn]
      exact map_sgn (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom ε i j)

theorem eq_sgn_of_submatrix {n r : ℕ} (hr : n = r) (h : r ≤ n) {S : Type} [CommRing S] {x : GL (Fin n) S} {ε : ℤˣ}
    (e : x.1.submatrix (Fin.castLE h) (Fin.castLE h) = (sgnGL r S ε).1) : x = sgnGL n S ε := by
  subst hr
  exact Units.ext e

theorem sign_calc {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {x z w₂ w₃ : Fin n → R} {M : ℕ} {ε : ℤˣ}
    (e₂ : x - K *ᵥ z = M • w₂) (e₃ : K *ᵥ z - (sgnGL n R ε).1 *ᵥ z = M • w₃) : x - (ε : ℤ) • z = M • (w₂ + w₃) := by
  rw [smul_add, ← e₂, ← e₃, sub_add_sub_cancel, sgnGL_val, Matrix.smul_mulVec, Matrix.one_mulVec]

variable {D : D7}

theorem finVec_sub_zsmul (V : HSp D) (x y : Fin V.rank → D.host.E) (e : ℤ) :
    finVec V (x - e • y) = finVec V x - e • finVec V y := by
  funext j
  exact (map_sub (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) (x j) (e • y j)).trans
    (congrArg (fun t => finVec V x j - t) (map_zsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) e (y j)))

theorem hatV_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) : GlobalTheory.Ker.hatV Λ = Formalism.L2.Pj.latHat V := by
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  rw [hl]; rfl

theorem mulVec_mem {V : HSp D} {k : GA D V} (hk : GlobalTheory.Member.FinCong V 1 k) :
    ∀ z ∈ Formalism.L2.Pj.latHat V, (finHom V k).1 *ᵥ z ∈ Formalism.L2.Pj.latHat V := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  rw [one_nsmul] at e
  rw [sub_eq_iff_eq_add.1 e]
  exact add_mem hy hz

theorem isMov_of_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {k : GA D V} (hk : Lev.finE V k ∈ St β) : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt V k) Λ Λ := by
  have hk' : Lev.finE V k⁻¹ ∈ St β := by rw [map_inv]; exact inv_mem hk
  have h1 := mulVec_mem (GlobalTheory.LevelAction.finCong_of_mem_St hβ hk)
  have h2 := mulVec_mem (GlobalTheory.LevelAction.finCong_of_mem_St hβ hk')
  intro u
  rw [hatV_eq hβ]
  change _ ↔ ∃ u₀ ∈ _, u = (finHom V k).1 *ᵥ u₀
  constructor
  · intro hu
    exact ⟨_, h2 u hu, by rw [← GlobalTheory.Member.LatMove.fin_mul, mul_inv_cancel, GlobalTheory.Member.LatMove.fin_one]⟩
  · rintro ⟨u₀, h0, rfl⟩
    exact h1 u₀ h0

theorem cong_on_half {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    {K K' : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ b ∈ J, ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) • (K *ᵥ z - K' *ᵥ z) = M • w) :
    ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      K *ᵥ finVec V (ι a) - K' *ᵥ finVec V (ι a) = M • w := by
  have hm : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  intro a ha
  refine Submodule.smul_induction_on ha (fun b hb a _ => ?_) ?_
  · obtain ⟨w, hw, e⟩ := h b hb _ ((GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hm a))
    have e₀ : finVec V (ι (b • a)) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • finVec V (ι a) := by
      rw [map_smul]; exact GlobalTheory.AdLat.Tower.fv_smul b (ι a)
    exact ⟨w, hw, by rw [e₀, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_sub, e]⟩
  · rintro x y ⟨w, hw, e⟩ ⟨w', hw', e'⟩
    have e₀ : finVec V (ι (x + y)) = finVec V (ι x) + finVec V (ι y) := by
      rw [map_add (f := _)]; funext i; exact TensorProduct.tmul_add _ _ _
    refine ⟨w + w', add_mem hw hw', ?_⟩
    rw [e₀, Matrix.mulVec_add, Matrix.mulVec_add, smul_add, ← e, ← e']
    abel

theorem mark_calc {R : Type} [CommRing R] {n : ℕ} {Hm K K' : Matrix (Fin n) (Fin n) R} {m x z w₁ w₂ w₃ : Fin n → R} {M : ℕ}
    (e₁ : m - Hm *ᵥ x = M • w₁) (e₂ : x - K *ᵥ z = M • w₂) (e₃ : K *ᵥ z - K' *ᵥ z = M • w₃) :
    m - Hm *ᵥ (K' *ᵥ z) = M • (w₁ + Hm *ᵥ (w₂ + w₃)) := by
  rw [smul_add, ← Matrix.mulVec_smul, smul_add, ← e₁, ← e₂, ← e₃, sub_add_sub_cancel, Matrix.mulVec_sub, sub_add_sub_cancel]

theorem exists_cong_sign {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k : GA D V}
    (hk : Lev.finE V k ∈ St β) (ε : ℤˣ)
    (h : ∀ P ∈ T, redFn β P (Lev.finE V k) = sgnGL _ _ ε) {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • ((finHom V k).1 *ᵥ z -
        (sgnGL V.rank (Af D.host.F ⊗[D.host.F] D.host.E) ε).1 *ᵥ z) = M • w := by
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := (hatV_eq hβ).symm
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_matrix_sign hfr T hJ hk ε h hb (K := (finHom V k).1) (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [← Matrix.sub_mulVec, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem redFn_sign {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (hr : V.rank = L.r)
    {g : G0 L.Pg L.r} {k : GA D V} (hk : Lev.IsLevelLift V β L g k) (ε : ℤˣ) (hg : ∀ P, g P = sgnGL _ _ ε) :
    ∀ P ∈ L.Pg, redFn β P (Lev.finE V k) = sgnGL _ _ ε := by
  intro P hP
  have e : upperLeftBlock L.hr (redFn β P (Lev.finE V k)) = g ⟨P, hP⟩ := congrFun hk.2.2 ⟨P, hP⟩
  have e' := congrArg Units.val (e.trans (hg ⟨P, hP⟩))
  rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP))] at e'
  exact eq_sgn_of_submatrix hr L.hr e'

theorem exists_div {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM : 0 < M) {a : La}
    {w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latGHat V 1) (e : finVec V (ι a) = M • w) :
    ∃ b, a = M • b := by
  have hm : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have h5 := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1
  obtain ⟨⟨v, hv⟩, ev⟩ := GlobalTheory.AdLat.Tower.exists_div (F := D.host.F) (M := latG V 1)
    (fun v => h5 ▸ (GlobalTheory.Member.LatMove.mem_lat_iff V 1 v).symm) hM ⟨_, hm a⟩ (h5 ▸ hw) e
  obtain ⟨c, rfl⟩ : v ∈ LinearMap.range ι := hι.2 ▸ hv
  refine ⟨c, hι.1 ?_⟩
  rw [map_nsmul]
  exact congrArg Subtype.val ev

theorem sign_div {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM : 0 < M) {a a' : La} {e : ℤ}
    {w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latGHat V 1)
    (h : finVec V (ι a') - e • finVec V (ι a) = M • w) : ∃ b, a' = e • a + M • b := by
  obtain ⟨b, hb⟩ := exists_div (a := a' - e • a) hι hM hw (by rw [map_sub, map_zsmul, finVec_sub_zsmul, h])
  exact ⟨b, by rw [← hb, add_sub_cancel]⟩

theorem mu_cast {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) {k : GA D W}
    {x : (AE D)ˣ} (hx : IsDetRoot W k x) : castDict hV mu k = ((χ x : Circle) : ℂ) := by
  subst hV
  exact h.2 k x hx

theorem mem_iff_prod_le {E : Type} [Field E] [NumberField E] (T : Finset (Pl E)) (P : Pl E) :
    P ∈ T ↔ ∏ Q ∈ T, Q.asIdeal ≤ P.asIdeal := by
  rw [P.isPrime.prod_le]
  refine ⟨fun h => ⟨P, h, le_rfl⟩, ?_⟩
  rintro ⟨Q, hQ, h⟩
  rwa [← HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)]

end GlobalTheory.OneMapRef.Lift
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published
open scoped Pointwise

namespace GlobalTheory.FrobTransfer

theorem pow_smul_sub_mem {G S : Type} [Group G] [CommRing S] [MulSemiringAction G S] {P : Ideal S} {σ : G} {q : ℕ}
    (h : ∀ x, σ • x - x ^ q ∈ P) (n : ℕ) (x : S) : σ ^ n • x - x ^ q ^ n ∈ P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := h (σ ^ n • x)
    rw [← Ideal.Quotient.eq] at h1 ih ⊢
    rw [pow_succ', mul_smul, h1, map_pow, ih, ← map_pow, ← pow_mul, pow_succ]

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem orderOf_eq_inertiaDeg {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) {P : Ideal (𝓞 L)} [hP : P.IsPrime]
    [hPo : P.LiesOver 𝔭.asIdeal] {σ : L ≃ₐ[K] L} (h : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P) :
    orderOf σ = P.inertiaDeg (𝓞 K) := by
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have : P.IsMaximal := hP.isMaximal hne
  let := Ideal.Quotient.field P
  let := Fintype.ofFinite (𝓞 L ⧸ P)
  have hc : Fintype.card (𝓞 L ⧸ P) = Ideal.absNorm 𝔭.asIdeal ^ P.inertiaDeg (𝓞 K) := by
    rw [Ideal.absNorm_pow_inertiaDeg, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hq : 1 < Ideal.absNorm 𝔭.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭
  have hf := Ideal.inertiaDeg_pos P (𝓞 K)
  apply le_antisymm
  · refine orderOf_le_of_pow_eq_one hf (hu _ ⟨P, hP, hPo, fun x => ?_⟩)
    have h1 := pow_smul_sub_mem h (P.inertiaDeg (𝓞 K)) x
    rw [← Ideal.Quotient.eq] at h1 ⊢
    rw [h1, map_pow, ← hc, FiniteField.pow_card]
  · have ho : 0 < orderOf σ := orderOf_pos σ
    have hlt : 1 < Ideal.absNorm 𝔭.asIdeal ^ orderOf σ := Nat.one_lt_pow ho.ne' hq
    have h2 := (FiniteField.forall_pow_eq_one_iff (𝓞 L ⧸ P) (Ideal.absNorm 𝔭.asIdeal ^ orderOf σ - 1)).1 fun u => by
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 L ⧸ P)
      have h1 := pow_smul_sub_mem h (orderOf σ) x
      rw [pow_orderOf_eq_one, one_smul, ← Ideal.Quotient.eq, map_pow, hx] at h1
      have h3 : u ^ Ideal.absNorm 𝔭.asIdeal ^ orderOf σ = u := Units.ext (by rw [Units.val_pow_eq_pow_val, ← h1])
      rw [pow_sub u hlt.le, h3, pow_one, mul_inv_cancel]
    have h4 := Nat.le_of_dvd (by omega) h2
    rw [hc] at h4
    exact (Nat.pow_le_pow_iff_right hq).1 (by omega)


omit [NumberField K] [NumberField L] in
theorem card_inertia {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) (P : Ideal (𝓞 L)) [hP : P.IsPrime]
    [hPo : P.LiesOver 𝔭.asIdeal] : Nat.card (P.inertia (L ≃ₐ[K] L)) = 1 := by
  have h1 : P.inertia (L ≃ₐ[K] L) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => hu τ ⟨P, hP, hPo, hτ⟩
  rw [h1, Subgroup.card_bot]

theorem stabilizer_eq [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) {P : Ideal (𝓞 L)}
    [hP : P.IsPrime] [hPo : P.LiesOver 𝔭.asIdeal] {σ : L ≃ₐ[K] L}
    (h : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P) :
    Subgroup.zpowers σ = MulAction.stabilizer (L ≃ₐ[K] L) P := by
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have hF : IsArithFrobAt (𝓞 K) σ P := by
    unfold IsArithFrobAt AlgHom.IsArithFrobAt
    rw [← hPo.over, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact h
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hF.mem_stabilizer) ?_
  rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := L ≃ₐ[K] L) 𝔭.asIdeal P, card_inertia hu, one_mul,
    Nat.card_zpowers, orderOf_eq_inertiaDeg hu h]

theorem map_eq_prod [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) :
    𝔭.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) = ∏ P : 𝔭.asIdeal.primesOver (𝓞 L), P.1 := by
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  rw [Ideal.map_algebraMap_eq_finsetProd_pow 𝔭.ne_bot, ← Finset.prod_set_coe]
  refine Finset.prod_congr rfl fun ⟨P, hP, hPo⟩ _ => ?_
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal P (L ≃ₐ[K] L),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P, card_inertia hu, pow_one]

theorem heckeIdeal_prod {ι : Type} (χ : (L ≃ₐ[K] L) →* ℂˣ) (s : Finset ι) (f : ι → Ideal (𝓞 K))
    (hf : ∀ i, f i ≠ 0) : heckeIdeal L χ (∏ i ∈ s, f i) = ∏ i ∈ s, heckeIdeal L χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.NT.Model.heckeIdeal_top L χ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      GlobalTheory.NT.Model.heckeIdeal_mul L χ (hf a) (Finset.prod_ne_zero_iff.2 fun i _ => hf i), ih]

variable {N : Type} [Field N] [NumberField N] [Algebra L N] [Algebra K N] [IsScalarTower K L N]

omit [NumberField K] [NumberField L] [NumberField N] in
theorem algebraMap_restrict_smul [Normal K L] (g : N ≃ₐ[K] N) (x : 𝓞 L) :
    algebraMap (𝓞 L) (𝓞 N) (AlgEquiv.restrictNormalHom L g • x) = g • algebraMap (𝓞 L) (𝓞 N) x :=
  RingOfIntegers.ext (g.restrictNormal_commutes L x)

omit [NumberField K] [NumberField L] [NumberField N] in
theorem under_inv_smul [Normal K L] (g : N ≃ₐ[K] N) (Q : Ideal (𝓞 N)) :
    (g⁻¹ • Q).under (𝓞 L) = (AlgEquiv.restrictNormalHom L g)⁻¹ • Q.under (𝓞 L) := by
  ext x
  rw [Ideal.mem_under, Ideal.mem_inv_pointwise_smul_iff, Ideal.mem_inv_pointwise_smul_iff, Ideal.mem_under,
    algebraMap_restrict_smul]


omit [NumberField K] [NumberField L] [NumberField N] in
theorem exists_restrictScalars [Normal K L] (g : N ≃ₐ[K] N) (hg : AlgEquiv.restrictNormalHom L g = 1) :
    ∃ τ : N ≃ₐ[L] N, τ.restrictScalars K = g := by
  refine ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun x => ?_, rfl⟩
  have := g.restrictNormal_commutes L x
  rw [show g.restrictNormal L = 1 from hg] at this
  exact this.symm


omit [NumberField K] [NumberField L] [NumberField N] in
theorem unramIn_top {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn N 𝔭) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver 𝔭.asIdeal] : UnramIn N P := by
  rintro τ ⟨Q, hQ, hQo, hτ⟩
  have := hu (τ.restrictScalars K) ⟨Q, hQ, Ideal.LiesOver.trans Q P.asIdeal 𝔭.asIdeal, hτ⟩
  exact AlgEquiv.ext fun x => DFunLike.congr_fun this x


omit [NumberField K] [NumberField L] [NumberField N] in
theorem minimalPeriod_eq [Normal K L] (σ : N ≃ₐ[K] N)
    (c : (N ≃ₐ[K] N) ⧸ (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker) :
    Function.minimalPeriod (σ • ·) c = orderOf (AlgEquiv.restrictNormalHom L σ) := by
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective c
  refine Nat.dvd_right_iff_eq.1 fun n => ?_
  rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, orderOf_dvd_iff_pow_eq_one, MulAction.Quotient.smul_mk,
    QuotientGroup.eq, MonoidHom.mem_ker, smul_eq_mul, map_mul, map_inv, map_mul, inv_mul_eq_one, mul_eq_right,
    map_pow]

theorem heckeIdeal_under [IsGalois K L] [IsGalois K N] [IsGalois L N] {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hu : UnramIn N 𝔭) {Q : Ideal (𝓞 N)} [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] {σ : N ≃ₐ[K] N}
    (h : ∀ x : 𝓞 N, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q) (χ : (N ≃ₐ[L] N) →* ℂˣ) (t : N ≃ₐ[K] N)
    (τ : N ≃ₐ[L] N) (hτ : τ.restrictScalars K = t⁻¹ * σ ^ (Q.under (𝓞 L)).inertiaDeg (𝓞 K) * t) :
    heckeIdeal N χ ((t⁻¹ • Q).under (𝓞 L)) = (χ τ : ℂˣ) := by
  let P : HeightOneSpectrum (𝓞 L) :=
    ⟨(t⁻¹ • Q).under (𝓞 L), inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _⟩
  have : P.asIdeal.LiesOver 𝔭.asIdeal := inferInstanceAs (((t⁻¹ • Q).under (𝓞 L)).LiesOver 𝔭.asIdeal)
  have := P.isPrime
  change heckeIdeal N χ P.asIdeal = _
  rw [GlobalTheory.NT.Model.heckeIdeal_prime]
  refine heckeVal_of_unramIn N χ (unramIn_top hu P) ⟨t⁻¹ • Q, inferInstance, ⟨rfl⟩, fun x => ?_⟩
  rw [← Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal P.asIdeal,
    ← Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal P.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal (Q.under (𝓞 L)) (L ≃ₐ[K] L), Ideal.mem_inv_pointwise_smul_iff,
    show τ • x = τ.restrictScalars K • x from rfl, hτ, smul_sub, smul_pow', ← mul_smul, mul_assoc,
    mul_inv_cancel_left, mul_smul]
  exact pow_smul_sub_mem h _ _

theorem heckeIdeal_map_eq_transfer : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N] [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L] [IsGalois K N] [IsAbelianGalois L N] (𝔭 : HeightOneSpectrum (𝓞 K)), GlobalTheory.NT.UnramIn N 𝔭 → ∀ σ : N ≃ₐ[K] N, GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ (χ : (N ≃ₐ[L] N) →* ℂˣ) (φ : (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker →* ℂˣ), (∀ (τ : N ≃ₐ[L] N) (h : τ.restrictScalars K ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker), φ ⟨τ.restrictScalars K, h⟩ = χ τ) → GlobalTheory.NT.heckeIdeal N χ (𝔭.asIdeal.map (algebraMap (𝓞 K) (𝓞 L))) = ((MonoidHom.transfer φ σ : ℂˣ) : ℂ) := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ _ _ 𝔭 hu σ ⟨Q, hQ, hQo, h⟩ χ φ hφ
  classical
  have huL : UnramIn L 𝔭 := GlobalTheory.RayMaximal.unramIn_of_tower hu
  let r := AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L
  have hL : ∀ x : 𝓞 L, r σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q.under (𝓞 L) := fun x => by
    rw [Ideal.mem_under, map_sub, map_pow, algebraMap_restrict_smul]
    exact h _
  have hst := stabilizer_eq huL hL
  have hord := orderOf_eq_inertiaDeg huL hL
  let := Fintype.ofFinite (Quotient (MulAction.orbitRel (Subgroup.zpowers σ) ((N ≃ₐ[K] N) ⧸ r.ker)))
  let e : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) ((N ≃ₐ[K] N) ⧸ r.ker)) → 𝔭.asIdeal.primesOver (𝓞 L) :=
    fun q => ⟨(q.out.out⁻¹ • Q).under (𝓞 L), inferInstance, inferInstance⟩
  have key : ∀ s t : N ≃ₐ[K] N, (s⁻¹ • Q).under (𝓞 L) = (t⁻¹ • Q).under (𝓞 L) ↔
      MulAction.orbitRel (Subgroup.zpowers σ) ((N ≃ₐ[K] N) ⧸ r.ker) (s : (N ≃ₐ[K] N) ⧸ r.ker) t := fun s t => by
    rw [under_inv_smul, under_inv_smul, inv_smul_eq_iff, ← mul_smul, eq_comm, ← MulAction.mem_stabilizer_iff, ← hst,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨⟨σ ^ k, k, rfl⟩, ?_⟩
      change ((σ ^ k * t : N ≃ₐ[K] N) : (N ≃ₐ[K] N) ⧸ r.ker) = s
      rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_zpow, hk, inv_mul_cancel_right,
        inv_mul_cancel]
    · rintro ⟨⟨_, k, rfl⟩, hk⟩
      change ((σ ^ k * t : N ≃ₐ[K] N) : (N ≃ₐ[K] N) ⧸ r.ker) = s at hk
      rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_zpow, inv_mul_eq_one] at hk
      exact ⟨k, by rw [← hk, mul_inv_cancel_right]⟩
  have he : Function.Bijective e := by
    constructor
    · intro q q' hq
      have := (key _ _).1 (congrArg Subtype.val hq)
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      exact Quotient.out_equiv_out.1 this
    · rintro ⟨P, hP, hPo⟩
      obtain ⟨γ, hγ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝔭.asIdeal (Q.under (𝓞 L)) P (L ≃ₐ[K] L)
      obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) N γ⁻¹
      refine ⟨Quotient.mk _ (g : (N ≃ₐ[K] N) ⧸ r.ker), Subtype.ext ?_⟩
      refine ((key _ g).2 ?_).trans (by rw [under_inv_smul, hg, inv_inv, hγ])
      rw [QuotientGroup.out_eq']
      exact Quotient.mk_out _
  rw [map_eq_prod huL, heckeIdeal_prod χ _ _ fun P => ?_, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Units.coe_prod]
  · refine (Fintype.prod_bijective e he _ _ fun q => ?_).symm
    obtain ⟨τ, hτ⟩ := exists_restrictScalars (L := L) _ (QuotientGroup.out_conj_pow_minimalPeriod_mem r.ker σ q.out)
    rw [heckeIdeal_under hu h χ q.out.out τ (by rw [hτ, minimalPeriod_eq, hord]),
      ← hφ τ (hτ ▸ QuotientGroup.out_conj_pow_minimalPeriod_mem r.ker σ q.out)]
    exact congrArg (fun x => ((φ x : ℂˣ) : ℂ)) (Subtype.ext hτ.symm)
  · have := P.2.2
    exact Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _

end GlobalTheory.FrobTransfer
end
end
