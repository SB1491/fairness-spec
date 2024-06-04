From sflib Require Import sflib.
From Paco Require Import paco.
From stdpp Require namespaces.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib
     PCM IProp IPM WMM FairLock
     Mod Linking SCM Red Weakest FancyUpdate.
     From PromisingLib Require Import Loc Event.
     From PromisingSEQ Require Import Time View TView Cell Memory Local.

From Fairness Require Import NatStructs.
Section WSPEC.


Variable ident_src: ID.
Variable state_src: Type.

Variable gvars : list nat.
Variable tgt_mod : Mod.t.

Context `{Σ: GRA.t}.

Context `{Invs : @InvSet Σ}.

Context `{MONORA: @GRA.inG monoRA Σ}.
Context `{THDRA: @GRA.inG ThreadRA Σ}.
Context `{STATESRC: @GRA.inG (stateSrcRA (unit)) Σ}.
Context `{IDENTSRC: @GRA.inG (identSrcRA (void)) Σ}.

Context `{STATETGT: @GRA.inG (stateTgtRA (OMod.closed_state tgt_mod (WMem.mod))) Σ}.
Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident tgt_mod (WMem.mod))) Σ}.

Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident tgt_mod (WMem.mod))) Σ}.
(*
Context `{STATETGT: @GRA.inG (stateTgtRA ((OMod.closed_state ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod)))) Σ}.
Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod))%type) Σ}.
Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod))%type) Σ}.*)
Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
Context `{EDGERA: @GRA.inG EdgeRA Σ}.
Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

Context `{COPSETRA : @GRA.inG CoPset.t Σ}.
Context `{GSETRA : @GRA.inG Gset.t Σ}.
Context `{INVSETRA : @GRA.inG (InvSetRA Var) Σ}.

Context `{WMEMRA: @GRA.inG wmemRA Σ}.

Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
Context `{EXCL2: @GRA.inG (Excl.t (unit * unit)) Σ}.
Context `{ONESHOTRA: @GRA.inG (OneShot.t nat) Σ}.
Context `{REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ}.
Context `{CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ}.
Context `{AUTHNRA: @GRA.inG (Auth.t (Excl.t nat)) Σ}.
Context `{AUTHVWRA: @GRA.inG (Auth.t (Excl.t View.t)) Σ}.
Context `{AUTHVWRA2: @GRA.inG (Auth.t (Excl.t (View.t * unit))) Σ}.
Context `{AUTHNMNRA: @GRA.inG (Auth.t (NatMapRALarge.t nat)) Σ}.


Lemma wload_fun_spec'
l v vw vw'
tid E R_src R_tgt (Q : R_src -> R_tgt -> iProp)
r g ps pt
itr_src ktr_tgt
st0 mem 
:
(St_tgt (st0, mem))
-∗
(wpoints_to l v vw)
-∗
(wmemory_black mem)
-*
(⌜View.le vw vw'⌝)
-∗
(∀vw'', St_tgt (st0, mem) -∗ (wpoints_to l v vw'') -∗ (⌜View.le vw' vw''⌝)
-∗
(wmemory_black mem)-∗ stsim tid E r g Q ps true itr_src (ktr_tgt (vw'', v)))
-∗
(stsim tid E r g Q ps pt itr_src
(map_event (OMod.emb_callee tgt_mod (WMem.mod)) (WMem.load_fun (vw', l, Ordering.plain)) >>= ktr_tgt))
.

Abort.

Lemma wload_fun_spec
l v vw vw'
tid E R_src R_tgt (Q : R_src -> R_tgt -> iProp)
r g ps pt
itr_src ktr_tgt
st0 mem 
:
(St_tgt (st0, mem))
-∗
(wpoints_to l v vw)
-∗
(wmemory_black mem)
-*
(⌜View.le vw vw'⌝)
-∗
(∀vw'', St_tgt (st0, mem) -∗ (wpoints_to l v vw'') -∗ (⌜View.le vw' vw''⌝)
-∗
(wmemory_black mem)-∗ stsim tid E r g Q ps true itr_src (ktr_tgt (vw'', v)))
-∗
(stsim tid E r g Q ps pt itr_src
(map_event (OMod.emb_callee tgt_mod (WMem.mod)) (WMem.load_fun (vw', l, Ordering.plain)) >>= ktr_tgt))
. 
Proof.
iIntros "ST_TGT WPOINTS_TO MEM_BLACK %VW Q".
rred. iApply stsim_getR.
iSplit. iFrame.
rred.
iApply stsim_chooseR. iIntros "%".
destruct x. destruct x as [[lc1 val] to]. des. rename y into READ. rred.
iPoseProof (wpoints_to_view_mon with "WPOINTS_TO") as "WPOINTS_TO". eapply VW.

iPoseProof (wmemory_ra_load with "MEM_BLACK WPOINTS_TO") as "[i1MEM [%VW2 >i0PTR]]".
eapply READ. eauto. eauto. des. subst val.
iApply stsim_fairR.
{  i. instantiate (1:= []). ss. clear - IN.
unfold prism_fmap, WMem.missed in IN. des_ifs.
}
{ i. instantiate (1:=[]) in IN. inv IN. }
{ econs. }
{ auto. }

iIntros "_ _". rred.


iPoseProof ("Q" with "[ST_TGT]") as "Q".
iFrame.
iPoseProof ("Q" with "[i0PTR]") as "Q".
iFrame.
iPoseProof ("Q" with "[i1MEM]") as "Q".
iFrame.
iFrame.
iFrame.
Qed.

Lemma wstore_fun_spec : True.
Abort.

Lemma wfaa_fun_spec : True.
Abort.



(*
(wmemory_black m)
-∗
(wpoints_to l v0 vw0)
-∗
((wmemory_black m) ∗ (⌜(View.le vw0 vw1) /\ (v0 = v1)⌝) ∗ #=>(wpoints_to l v0 vw1))
*)
End WSPEC.