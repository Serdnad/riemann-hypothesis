module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CongruenceMaxGalois

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

variable (D : D7)

abbrev GalE : Type := G D.host.E D.nd.Om

def IsGaloisRepOf {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (φ : GalE D),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) φ →
    ((r φ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
      galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))

end GlobalTheory.IndefiniteRowSideFullHecke.CongruenceMaxGalois

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open scoped ENNReal Matrix

def len_vp (O : Type) [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] : ℝ≥0∞ :=
  (Module.length O M : ℝ≥0∞) / (Module.length O (O ⧸ Ideal.span {(l : O)}) : ℝ≥0∞)

def val_vp {O : Type} [CommRing O] (l : ℕ) (x : O) : ℝ≥0∞ :=
  len_vp O l (O ⧸ Ideal.span {x})

section Rep

variable {Γ A : Type} [Group Γ] [CommRing A] {m : ℕ}

end Rep

section Div

variable {Γ O' : Type} [Group Γ] [CommRing O'] [IsDomain O'] {m : ℕ}

end Div

section BK

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

def IsCrysCocycle (T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀) (f : ↥Gw → Fin m → O₀) : Prop :=
  (fun (g : ↥(Loc.GK Bw.Kw)) (j : Fin m) => Bw.toLL (f (Bw.e.symm g) j)) ∈
    Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))

variable {O' : Type} [CommRing O'] [IsDomain O'] (ι : O₀ →+* O')

end BK

def IsWildAt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (σ : G E Ω) : Prop :=
  ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1

section HidaSetting

variable (D : D7) (i : D.ntw.Tw)

abbrev GE : Type := G D.host.E D.nd.Om

abbrev decAt (v : PlE D.host) : Subgroup (GE D) := Dec (F := D.host.E) (D.nd.plOm.1 v)

abbrev ineAt (v : PlE D.host) : Subgroup (GE D) := Ine (F := D.host.E) (D.nd.plOm.1 v)

def InertiaBound (ε' : ℝ) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : GE D →* (D.ntw.Ok i k)ˣ) : Prop :=
  ∀ γ : PlE D.host → GE D, (∀ P ∈ Q, TameGenAt (D.nd.plOm.1 P) (γ P)) →
    (D.R.t : ℝ≥0∞) * ∑ P ∈ Q, val_vp (D.ntw.l i) (((ψ (γ P) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) - 1) ≤
      ENNReal.ofReal ε'

end HidaSetting

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG

def SplitsCompletely (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  p.Prime ∧ (Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E

theorem splitsCompletely_g (D : D7) (i : Fin 2) : SplitsCompletely D.host.E (D.host.g i) :=
  ⟨D.host.g_prime i, D.nd.g_split i⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

def nlen {O : Type} [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] : WithTop ℚ :=
  if Module.length O M = ⊤ then ⊤ else ((lenUnit (O := O) l M : ℚ) : WithTop ℚ)

section Ext

variable {O₀ O' : Type} [CommRing O₀] [IsDomain O₀] [CommRing O'] [IsDomain O']
  (f : O₀ →+* O') (hf : Function.Injective f)

def fracMap : FractionRing O₀ →+* FractionRing O' :=
  IsFractionRing.map (A := O₀) (B := O') (K := FractionRing O₀) (L := FractionRing O') hf

theorem fracMap_alg (c : O₀) :
    fracMap f hf (algebraMap O₀ (FractionRing O₀) c) = algebraMap O' (FractionRing O') (f c) := by
  simp [fracMap, IsFractionRing.map]

def vecMap (k : ℕ) : (Fin k → FractionRing O₀) →ₛₗ[f] (Fin k → FractionRing O') where
  toFun v j := fracMap f hf (v j)
  map_add' u v := by
    funext j
    simp
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, fracMap_alg]

def pushKO (k : ℕ) : KOG O₀ k →ₛₗ[f] KOG O' k :=
  Submodule.mapQ _ _ (vecMap f hf k) (by
    rintro _ ⟨u, rfl⟩
    refine ⟨fun j => f (u j), ?_⟩
    funext j
    exact (fracMap_alg f hf (u j)).symm)

def extCond {Γ : Type} [Group Γ] [TopologicalSpace Γ] {k : ℕ}
    (ρ₀ : Representation O₀ Γ (KOG O₀ k)) (L₀ : Submodule O₀ (H1 ρ₀))
    (ρ' : Representation O' Γ (KOG O' k)) : Submodule O' (H1 ρ') :=
  ((Submodule.span O' {c : Γ → KOG O' k | ∃ c₀ : Z1 ρ₀, Submodule.Quotient.mk c₀ ∈ L₀ ∧
      c = fun g => pushKO f hf k ((c₀ : Γ → KOG O₀ k) g)}).comap (Z1 ρ').subtype).map
    (Submodule.mkQ _)

end Ext

def SameChar {O₀ O₁ O₂ Γ : Type} [CommRing O₀] [CommRing O₁] [CommRing O₂] [Group Γ]
    (f₁ : O₀ →+* O₁) (f₂ : O₀ →+* O₂) (ψ₁ : Γ →* O₁ˣ) (ψ₂ : Γ →* O₂ˣ) : Prop :=
  ∀ F : Γ →₀ O₀, (F.sum fun g c => f₁ c * ((ψ₁ g : O₁ˣ) : O₁)) = 0 ↔
    (F.sum fun g c => f₂ c * ((ψ₂ g : O₂ˣ) : O₂)) = 0

section Tw

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} (tw : NTw R H what₂ LL0 N)

def latT (i : tw.Tw) (s : tw.Sig i) : GE N →* Matrix (Fin R.r) (Fin R.r) (tw.O0 i) :=
  twistM ((Units.coeHom _).comp (tw.rhoS i s)) (tw.chi1 i (tw.jS i s) (tw.side i s))⁻¹

def setS (i : tw.Tw) : Set (PlE H) :=
  {v | ((∃ k, v ∈ placesOver H.E (H.g k)) ∨ v ∈ tw.pD i) ∧ v ∉ placesOver H.E (tw.l i)}

def latTpsi (i : tw.Tw) (s : tw.Sig i) {O' : Type} [CommRing O'] (f : tw.O0 i →+* O')
    (ψ : GE N →* O'ˣ) : GE N →* Matrix (Fin R.r) (Fin R.r) O' :=
  twistM (mapM f (latT tw i s)) ψ⁻¹

variable {tw} (L : LocTheory) (nbt : Br.NBrTw tw) (i : tw.Tw) (s : tw.Sig i)
  (Q : Finset (PlE H)) {O' : Type} [CommRing O'] [IsDomain O'] (f : tw.O0 i →+* O')
  (hf : Function.Injective f) (ψ : GE N →* O'ˣ)


open Classical in
def condL : ∀ v, Submodule O'
    (H1 ((WKG (latTpsi tw i s f ψ)).comp (Dec (F := H.E) (N.plOm.1 v)).subtype)) :=
  fun v => if h : v ∈ placesOver H.E (tw.l i) then
    extCond f hf ((WKG (latT tw i s)).comp (decS N v)) (Br.bkTw L nbt i v h (latT tw i s))
      ((WKG (latTpsi tw i s f ψ)).comp (Dec (F := H.E) (N.plOm.1 v)).subtype)
  else ⊤

def selT : Submodule O' (H1 (WKG (latTpsi tw i s f ψ))) :=
  Formalism.GaloisCohomology.SelAll (WKG (latTpsi tw i s f ψ)) N.plOm
    (Formalism.GaloisCohomology.bkCond (WKG (latTpsi tw i s f ψ)) N.plOm (tw.l i) (setS tw i ∪ ↑Q)
      (condL L nbt i s f hf ψ))

def sT : WithTop ℚ := nlen (O := O') (tw.l i) ↥(selT L nbt i s Q f hf ψ)

variable (tw)

def toOk (i : tw.Tw) (k : ℕ) : tw.O0 i →+* tw.Ok i k :=
  (algebraMap (tw.O i) (tw.Ok i k)).comp (algebraMap (tw.O0 i) (tw.O i))

theorem toOk_inj (i : tw.Tw) (k : ℕ) : Function.Injective (toOk tw i k) :=
  (tw.Ok_inj i k).comp (tw.O_inj i)

theorem twO_inj (a : N.Loc) : Function.Injective (tw.twist₂ a) := by
  haveI : CharZero (FractionRing (N.O a)) := (N.embK a).charZero_iff (N.embK a).injective |>.1 inferInstance
  haveI : CharZero (N.O a) := (algebraMap (N.O a) (FractionRing (N.O a))).charZero
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hp : (RingHom.ker (tw.twist₂ a)).IsPrime := RingHom.ker_isPrime _
  have hm : (RingHom.ker (tw.twist₂ a)).IsMaximal := hp.isMaximal hne
  have he := IsLocalRing.eq_maximalIdeal hm
  haveI := tw.twistBaseCoefficientRing_residueField_finite (tw.twOf a)
  haveI := Fintype.ofFinite (IsLocalRing.ResidueField (tw.O0 (tw.twOf a)))
  have h0 : ((Fintype.card (IsLocalRing.ResidueField (tw.O0 (tw.twOf a))) : ℕ) :
      IsLocalRing.ResidueField (tw.O0 (tw.twOf a))) = 0 := FiniteField.cast_card_eq_zero _
  have h1 : ((Fintype.card (IsLocalRing.ResidueField (tw.O0 (tw.twOf a))) : ℕ) :
      tw.O0 (tw.twOf a)) ∈ RingHom.ker (tw.twist₂ a) := by
    rw [he, ← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact h0
  rw [RingHom.mem_ker, map_natCast, Nat.cast_eq_zero] at h1
  exact Fintype.card_ne_zero h1

end Tw

section Rec

variable (D : D7)

def sPiTop (a : D.nd.Loc) (ρ : D.nd.X a → (GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (π : D.nd.X a) :
    WithTop ℚ :=
  nlen (O := D.nd.O a) (D.nd.l a) ↥(Br.selPi D.loc D.nbr a ρ π)

def sTLoc (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) : WithTop ℚ :=
  sT D.loc D.ntwbr (D.ntw.twOf a) s (D.nd.Q a) (D.ntw.twist₂ a) (twO_inj D.ntw a) (D.ntw.psiL a)

def IsRhoPt (a : D.nd.Loc) (π : D.nd.X a) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a))) ∧
  ∃ r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O a), IsHeckeGalois D.nd a π r ∧
    ∃ e : (Fin D.R.nV → KK D.nd a) ≃ₗ[KK D.nd a] ((Fin D.R.r → KK D.nd a) × (Fin D.R.t → KK D.nd a)),
      ∀ g u, e ((mapM (toK D.nd a) ((Units.coeHom _).comp r) g).mulVec u) =
        ((mapM (toK D.nd a) ((Units.coeHom _).comp ρ) g).mulVec (e u).1,
          fun c : Fin D.R.t =>
            toK D.nd a ((D.nd.chi a ((c : ℕ) + 1) g : (D.nd.O a)ˣ) : D.nd.O a) * (e u).2 c)

def GoodRowOf (j : ℕ) (σ : D.what₂.FT) : Prop := D.nd.goodRow σ ∧ D.what₂.isot j σ ≠ ⊥

def IsTriple (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)) : Prop :=
  D.ntw.jS _ s = D.nd.j a ∧ D.ntw.side _ s = D.ntw.twSide a ∧
  IsSSRep (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))
    (D.ntw.rhoS _ s)) ∧
  ∀ᶠ w in Filter.cofinite, SplitOut D.nd a w →
    ∀ (B : ValuationSubring D.nd.Om) (γ : GE D.nd), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) γ →
      ((D.ntw.rhoS _ s γ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly.map
          ((iotaO D.nd D.naut a).comp (D.ntw.twist₂ a)) =
        galPol D.naut (D.naut.lpTw (isoLoc D.nd D.naut (twistIso D.nd D.naut Sg D.naut.etaTinv) w)
          ((1 - (D.R.nV : ℝ)) / 2))

def AllTriples : Prop :=
  ∀ (a : D.nd.Loc) (σ : D.what₂.FT) (Sg : List (Part D.naut.CG)), GoodRowOf D (D.nd.j a) σ →
    HasParamW D.nd D.naut a σ Sg → ∃ s, IsTriple D a s Sg

def Attached (a : D.nd.Loc) (π : D.nd.X a) (s : D.ntw.Sig (D.ntw.twOf a)) : Prop :=
  ∃ (σ : D.what₂.FT) (Sg : List (Part D.naut.CG)), GoodRowOf D (D.nd.j a) σ ∧
    HasParamW D.nd D.naut a σ Sg ∧ HasParamX D.nd D.naut a π Sg ∧ IsTriple D a s Sg

end Rec

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting

open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

variable (D : D7)

def cE : ℕ := D.host.QS * D.host.q * D.host.d

def cEIdeal : Ideal (𝓞 D.host.K) := Ideal.span {((cE D : ℕ) : 𝓞 D.host.K)}

def Admissible (g : ℕ) : Prop :=
  g.Prime ∧ ∃ π : 𝓞 D.host.K, π - 1 ∈ cEIdeal D ∧ Algebra.norm ℤ π = (g : ℤ)

def AdmissiblePrimesWithConstant (c₁ : ℝ) : Prop :=
  ∀ (N : ℕ) (X : ℝ), c₁ ≤ (cE D : ℝ) → c₁ ≤ (D.host.d : ℝ) → 21 ≤ N → 0 < X →
    (N : ℝ) ^ 4 * (cE D : ℝ) ^ 500 ≤ (X / (cE D : ℝ) ^ 20) ^ ((1 : ℝ) / 4) →
    Real.log X ≤ (cE D : ℝ) →
    ∃ Y : ℝ, X / (cE D : ℝ) ^ 20 ≤ Y ∧ Y ≤ X / 2 ∧
      (∃ g₁ g₂ : ℕ, g₁ ≠ g₂ ∧ Admissible D g₁ ∧ Admissible D g₂ ∧
        Y ≤ g₁ ∧ (g₁ : ℝ) ≤ 2 * Y ∧ Y ≤ g₂ ∧ (g₂ : ℝ) ≤ 2 * Y ∧
        Formalism.CyclotomicNorms.BB N g₁ ∩ Formalism.CyclotomicNorms.BB N g₂ = ∅) ∧
      Y / (cE D : ℝ) ^ 20 ≤ (({g : ℕ | Admissible D g ∧ Y ≤ g ∧ (g : ℝ) ≤ 2 * Y}).ncard : ℝ)

abbrev GalE : Type := G D.host.E D.nd.Om

def OnW (σ : D.what₂.FT) : Prop := ∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ D.what₂.isot j σ ≠ ⊥

def OccursOnLevelZero (σ : D.what₂.FT) : Prop := (∃ a, D.what₂.ft a = σ) ∨ ∃ a, D.what₂.ft0 a = σ

def IsBaseChange (σ : D.what₂.FT) (Sig : List (Part D.naut.CG)) : Prop :=
  (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
  rankIso D.nd D.naut Sig = D.R.r ∧
  (∀ τ, (isoInf D.nd D.naut Sig τ).Nodup ∧ ∀ z ∈ isoInf D.nd D.naut Sig τ, ∃ n : ℤ, z = (n : ℂ)) ∧
  (∀ i : D.nd.Loc, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → ∀ w, IsSplitPl D.host w →
    isoLoc D.nd D.naut Sig w = D.naut.locW i σ w) ∧
  (∀ k v, D.nd.lab k σ v =
    D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) ∧
  D.ntypes.bc σ = Multiset.ofList (Sig.map fun p => (p.a, p.d))

def IsGaloisRepOf {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ w : PlE D.host, w ∉ placesOver D.host.E l →
    (∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        D.naut.inePol (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) s) ∧
    (D.naut.mono0 (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) ↔
      (r '' (Ine (F := D.host.E) (D.nd.plOm.1 w) : Set (GalE D))).Finite) ∧
    (D.naut.unr (D.naut.locG π w) → ∀ (B : ValuationSubring D.nd.Om) (s : GalE D),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) s →
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)))

def Zbar (l : ℕ) [Fact l.Prime] : Subring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : Qbar l)‖ ≤ 1; simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : Qbar l)‖ ≤ 1; simp
  neg_mem' {a} ha := by show ‖-a‖ ≤ 1; rwa [norm_neg]

def IsReduction {a l : ℕ} [Fact l.Prime] (red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l)
    (r : GalE D →* GL (Fin a) (Qbar l)) (ρ : GalE D →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Prop :=
  IsOpen (ρ.ker : Set (GalE D)) ∧ IsSSRep ρ ∧ ∀ g, ∃ p : (Zbar l)[X],
    p.map (Zbar l).subtype = ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly ∧
    p.map red = ((ρ g : GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar l)).charpoly

def ResidualTie (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  ∀ w : D.what₂.places.Pl,
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    ∃ (ι : Qbar (D.what₂.places.resChar w) ≃+* ℂ)
      (red : Zbar (D.what₂.places.resChar w) →+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w))
      (r : GalE D →* GL (Fin D.R.r) (Qbar (D.what₂.places.resChar w))),
      (∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val w x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1) ∧
      IsGaloisRepOf D π _ ι r ∧ IsReduction D red r (D.ntypes.rbar σ w) ∧
      ∀ k, D.what₂.places.resChar w ≠ D.host.g k → ∀ (v : D.nd.PlG k) x, x ≠ 0 →
        ∀ z : Zbar (D.what₂.places.resChar w), (z : Qbar _) = ι.symm (D.ntypes.teichC k x) →
          red z = D.ntypes.iota k v w x

def toFb (k : Fin 2) (c : (ZMod (D.host.g k))ˣ) : Fb (D.host.g k) (D.host.g_prime k) :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (c : ZMod (D.host.g k))

def LabelLaws : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (L : D.naut.LP (D.naut.plGw k v)),
    (D.naut.items₂ k _ L).Monic ∧ (D.naut.items₂ k _ L).natDegree ≤ D.naut.lpDim L ∧
    (∀ s : ℝ, D.naut.items₂ k _ (D.naut.lpTw L s) = D.naut.items₂ k _ L) ∧
    (∀ χ : D.naut.LP (D.naut.plGw k v), D.naut.lpDim χ = 1 → D.naut.unr χ →
      D.naut.items₂ k _ (D.naut.lpChar L χ) = D.naut.items₂ k _ L) ∧
    ((D.naut.items₂ k _ L).natDegree = D.naut.lpDim L →
      ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
        s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) →
        D.naut.inePol L s = (X - 1) ^ D.naut.lpDim L)

def BaseChangeRows : Prop :=
  ∀ σ, OnW D σ → ∃ Sig, IsBaseChange D σ Sig ∧ ∀ π, Sig = [⟨D.R.r, π, 1⟩] → ResidualTie D σ π

def TransferRows : Prop :=
  ∀ σ, OccursOnLevelZero D σ → (∀ v, Squarefree (D.nd.lab 0 σ v)) →
    (∀ a, 0 < a → a < D.R.r → ∃ v, ¬ ∃ q, q ∣ D.nd.lab 0 σ v ∧ q.natDegree = a) →
    D.what₂.isot D.R.m σ ≠ ⊥

def GaloisReps : Prop :=
  ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ r, IsGaloisRepOf D π l ι r

end GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting
end
end
