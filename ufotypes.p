% Formal characterization of Endurant Types in UFO
% João Paulo A. Almeida, Apr-2018
% Contributions from Giancarlo Guizzardi, Claudenir M. Fonseca, Daniele Porello, 
% Tiago Prince Sales, Alessander B. Benevides

% Use theorem provers at http://www.tptp.org/cgi-bin/SystemOnTPTP

%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Concerning instantiation and specialization

% Types are those entities that are possibly instantiated
fof(dtype_, axiom, (
	![X] : (type_(X) <=> (~world(X) & ?[W,Y] : (world(W) & iof(Y,X,W)) ) )
	)).

% Individuals are those entities that are necessarily not instantiated
fof(dindividual, axiom, (
	![X] : (individual(X) <=> (~world(X) & ![W] : (world(W) => ~?[Y] : (iof(Y,X,W)))) )
	)).
	
% We are only concerned with first-order types
fof(twolevel, axiom, (
	![X,Y,W] : (iof(X,Y,W) => (individual(X) & type_(Y) & world(W)))
	)).	
		
%fof(disjointnessCompletenessTop, conjecture, (
%	![X]: (world(X)|type_(X)|individual(X)) &
%	![X]: (world(X)=>(~type_(X)&~individual(X))) &
%	~?[X]: (world(X)&type_(X)) &
%	~?[X]: (world(X)&individual(X)) &
%	~?[X]: (type_(X)&individual(X)) 
%)).

% Specialization definition
fof(dspecialization, axiom, (
	![T1,T2] :
	(specializes(T1,T2) <=> (type_(T1)&type_(T2) & 
			![W]: (world(W)=> ![E]:(iof(E,T1,W) => iof(E,T2,W)))))
	)).

% Specialization is quasi-reflexive
%fof(specQuasiReflexive, conjecture, (
%	![X] : (type_(X)=>specializes(X,X))
%)).

% Specialization is transitive
%fof(specTransitive, conjecture, (
%	![X,Y,Z] : ((specializes(X,Y)&specializes(Y,Z))=>specializes(X,Z))
%)).

% Whenever two types have a common instance, they must share a supertype or a subtype for this instance
fof(nondisjointSameTaxonomy, axiom, (
	![T1,T2]: (![X,W]: ((iof(X,T1,W)&iof(X,T2,W)&~specializes(T1,T2)&~specializes(T2,T1))=> 
		(
			(?[T3]: (specializes(T1,T3)&specializes(T2,T3)&iof(X,T3,W)))|
			(?[T3]: (specializes(T3,T1)&specializes(T3,T2)&iof(X,T3,W)))
		)
		))
)).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Concerning rigidity 

% Definition of rigid type
fof(drigid, axiom, (
	![T]: (rigid(T)<=>(type_(T) &  
					(![X]: ((?[W]: (world(W) & iof(X,T,W))) => (![W2]: (world(W2)=>iof(X,T,W2)))))))
)).

% Definition of antirigid type
fof(dantirigid, axiom, (
	![T]: (antirigid(T)<=>(type_(T) &  
					(![X]: ((?[W]: (world(W) & iof(X,T,W))) => (?[W2]: (world(W2)&~iof(X,T,W2)))))))
)).

% Implicit definition of semirigid type 
fof(semirigid, axiom, (
	![T]: (semirigid(T)<=>(type_(T) &  
					~antirigid(T) & ~rigid(T)))
)).

% type_s are either rigid, anti-rigid or semi-rigid
%fof(completenessRigidity, conjecture, (
%	![T]: (type_(T)<=>(rigid(T)|semirigid(T)|antirigid(T))) 
%)).

% theorem
%fof(disjointnessRigidity, conjecture, (
%	~?[X]: ((rigid(X)&antirigid(X)) | (rigid(X)&semirigid(X)) | (semirigid(X)&antirigid(X))) 
%)).

% theorem
%fof(rigidCannotSpecializeAntirigid, conjecture, (
%	~?[X,Y]: (rigid(X)&antirigid(Y)&specializes(X,Y)) 
%)).

% theorem
%fof(semiridigCannotSpecializeAntirigid, conjecture, (
%	~?[X,Y]: (semirigid(X)&antirigid(Y)&specializes(X,Y)) 
%)).


%%%%%%%%%%%%%%%%%%%%%%%% Concerning sortality 

% Every *individual* necessarily instantiates a kind  // imply kinds are rigid!
fof(individualKindMin, axiom, (
	![X] : (individual(X) => ?[K]:(kind(K) & ![W]: (world(W)=>iof(X,K,W))))
	)).

% Every thing instantiates at most one kind (whenever it instantiates a kind it does not 
% possible instantiate a different one 
fof(individualKindMax, axiom, (
	![X,K,W] : ( ( kind(K) & iof(X,K,W)) =>
				(~?[Z,W2]: (~(Z=K) & kind(Z) & iof(X,Z,W2))) )
	)).

% Sortals definition, sortals are those types whose instances instantiate the same kind
fof(dsortal, axiom, (
	![T] :
	( sortal(T) <=> (type_(T) & 
					(?[K] : (kind(K) & ![X,W]: (world(W)=>(iof(X,T,W) => iof(X,K,W) )))) )) 
	)).

% A non-sortal is a type that is not a sortal 

fof(dnonsortal, axiom, (
	![T] : ( nonsortal(T) <=> (type_(T) & ~sortal(T)) ) 
	)).

% A non-sortal is a type that is not a sortal
%fof(dnonsortal2, conjecture, (
%	![T] : ( (type_(T) & sortal(T))=> ~nonsortal(T) ) 
%	)).
	
%%%%%% theorems

% kinds are rigid
%fof(kindsAreRigid, conjecture, (
%	![K]: (kind(K)=>rigid(K)) &	
%)).

% kinds are disjoint
%fof(kindsAreDisjoint, conjecture, (
%	![X,Y] : ( (kind(X)&kind(Y)&~(X=Y)) => (![W]: (world(W) => ~?[Z]:( iof(Z,X,W)&iof(Z,Y,W)))))
%)).
	
% kinds are sortals
%fof(kindsAreSortals, conjecture, (
%	![T] : (kind(T)=>sortal(T))
%)).

% sortals specialize one kind
%fof(sortalsSpecializeOneKindMin, conjecture, (
%	![X] : (sortal(X)=>?[K]:(kind(K)&specializes(X,K)))
%)).

% sortals cannot specialize different kinds
%fof(sortalsSpecializeOneKindMax, conjecture, (
%	~?[X,Y,Z]: (kind(Y)&kind(Z)&~(Y=Z)&specializes(X,Y)&specializes(X,Z))	
%)).

% a kind cannot specialize a different kind
%fof(kindCannotSpecializeKind, conjecture, (
%	~?[X,Y]: (kind(X)&kind(Y)&~(X=X)&specializes(X,Y))	
%)).

% a non-sortal cannot specialize a sortal
%fof(nonSortalCantSpecializeSortal, conjecture, (
%	~?[X,Y]: (nonsortal(X)&sortal(Y)&specializes(X,Y))
%)).

% Theorem: nonsortals do not have direct instances, their instances are also instances
% of a sortal that either: 
% specializes the nonsortal, or 
% specializes a common nonsortal supertype
%fof(nonsortalsNoDirectInstance, conjecture, (
%	![T,X,W]: (
%		(nonsortal(T) & iof(X,T,W)) =>
%		(
%			(?[S]: (sortal(S)&specializes(S,T)&iof(X,S,W))) |
%			(?[N,S]: (nonsortal(N)&sortal(S)&specializes(S,N)&specializes(T,N)&iof(X,S,W)))
%		)
%	)
%)).


%%%%%%%%%%% Concerning the leaf elements of the taxonomy of types in UFO

% Kinds and subkinds together encompass all rigid sortals
fof(kindsSubkinds, axiom, (
	![T]: ((kind(T)|subkind(T))<=>(rigid(T)&sortal(T)))
)).

% Kind and subkind are disjoint
fof(kindSubkindDisjoint, axiom, (
	~?[T]: (kind(T)&subkind(T))
)).

% Phase and roles together encompass all antirigid sortals
fof(phasesRoles, axiom, (
	![T]: ((phase(T)|role(T))<=>(antirigid(T)&sortal(T)))
)).

% They are disjoint
fof(phaseRoleDisjoint, axiom, (
	~?[T]: (phase(T)&role(T))
)).

% Semi rigid sortals are those that are semirigid and sortal
fof(dsemirigidSortal, axiom, (
	![T]: (semirigidsortal(T)<=>(semirigid(T)&sortal(T)))
)).

% Categories are those types that are rigid and non-sortals
fof(dcategory, axiom, (
	![T]: (category(T)<=>(rigid(T)&nonsortal(T)))
)).

% Mixins are those types that are semirigid and non-sortals
fof(dmixin, axiom, (
	![T]: (mixin(T)<=>(semirigid(T)&nonsortal(T)))
)).

% Phase and roles together encompass all antirigid nonsortals
fof(phaseRoleMixins, axiom, (
	![T]: ((phasemixin(T)|rolemixin(T))<=>(antirigid(T)&nonsortal(T)))
)).

% They are disjoint
fof(phaseRoleMixinDisjoint, axiom, (
	~?[T]: (phasemixin(T)&rolemixin(T))
)).

% Theorem: Leaf categories of UFO taxonomy of types are disjoint
%fof(leafNodesTaxonomyTypesDisjoint, conjecture, (
%	![T]: (kind(T)=>(~subkind(T)&~role(T)&~phase(T)&~rolemixin(T)&~phasemixin(T)&~category(T)&~mixin(T))) &
%	![T]: (subkind(T)=>(~kind(T)&~role(T)&~phase(T)&~rolemixin(T)&~phasemixin(T)&~category(T)&~mixin(T))) &
%	![T]: (role(T)=>(~kind(T)&~subkind(T)&~phase(T)&~rolemixin(T)&~phasemixin(T)&~category(T)&~mixin(T))) &
%	![T]: (phase(T)=>(~kind(T)&~subkind(T)&~role(T)&~rolemixin(T)&~phasemixin(T)&~category(T)&~mixin(T))) &
%	![T]: (rolemixin(T)=>(~kind(T)&~subkind(T)&~role(T)&~phase(T)&~phasemixin(T)&~category(T)&~mixin(T))) &
%	![T]: (phasemixin(T)=>(~kind(T)&~subkind(T)&~role(T)&~phase(T)&~rolemixin(T)&~category(T)&~mixin(T))) &
%	![T]: (category(T)=>(~kind(T)&~subkind(T)&~role(T)&~phase(T)&~rolemixin(T)&~phasemixin(T)&~mixin(T))) &
%	![T]: (mixin(T)=>(~kind(T)&~subkind(T)&~role(T)&~phase(T)&~rolemixin(T)&~phasemixin(T)&~category(T))) 
%)).	

% Leaf  Leaf categories of UFO taxonomy of types are complete
%fof(leafNodesTaxonomyTypesComplete, conjecture, (
%	![T]: (type_(T)<=>(kind(T)|subkind(T)|role(T)|phase(T)|semirigidsortal(T)|mixin(T)|rolemixin(T)|phasemixin(T)|category(T))) 
%)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Concerning the taxonomy of endurant (individuals)

% Endurants are individuals
fof(endurantsAreIndividuals, axiom, (
	![X]: (endurant(X)=>individual(X))
)).

% Substantials and moments together encompass endurants
fof(substantialsMoments, axiom, (
	![X]: ((substantial(X)|moment(X))<=>endurant(X))
)).

% Substantial and moment are disjoint
fof(substantialMomentDisjoint, axiom, (
	~?[X]: (substantial(X)&moment(X))
)).

% Relators and intrinsic moments together encompass moments
fof(relatorsIntrinsicMoments, axiom, (
	![X]: (moment(X)<=>(relator(X)|intrinsicmoment(X)))
)).

% Relator and intrinsic moment are disjoint
fof(relatorIntrinsicMomentDisjoint, axiom, (
	~?[X]: (relator(X)&intrinsicmoment(X))
)).

% Modes and qualities together encompass intrinsic moments
fof(modesQualities, axiom, (
	![X]: (intrinsicmoment(X)<=>(mode(X)|quality(X)))
)).

% Mode and quality are disjoint
fof(modeQualityDisjoint, axiom, (
	~?[X]: (mode(X)&quality(X))
)).

% Leaf nodes of the taxonomy of endurants are disjoint and together emcompass all endurants
%fof(disjointnessEndurants, conjecture, (
%	![X]: (substantial(X)=>(~relator(X)&~mode(X)&~quality(X))) &
%	![X]: (relator(X)=>(~substantial(X)&~mode(X)&~quality(X))) &
%	![X]: (mode(X)=>(~substantial(X)&~relator(X)&~quality(X))) &
%	![X]: (quality(X)=>(~substantial(X)&~relator(X)&~mode(X))) &
%	![X]: (endurant(X)<=>(substantial(X)|relator(X)|mode(X)|quality(X)))
%)).

%%%%%%%%%%%%%%%%%%%%%%%%%% Taxonomy of endurant types according to the ontological nature of their instances

% Endurant types are all those types whose instances are endurants
fof(dendurantType, axiom, (
	![T]: (enduranttype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>endurant(X)))))
)).

% Substantial types are all those types whose instances are substantials
fof(dsubstantialType, axiom, (
	![T]: (substantialtype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>substantial(X)))))
)).

% Moment types are all those types whose instances are moments
fof(dmomentType, axiom, (
	![T]: (momenttype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>moment(X)))))
)).

% Relator types are all those types whose instances are relators
fof(drelatorType, axiom, (
	![T]: (relatortype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>relator(X)))))
)).

% Mode types are all those types whose instances are modes
fof(dmodeType, axiom, (
	![T]: (modetype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>mode(X)))))
)).

% Quality types are all those types whose instances are qualities
fof(dqualityType, axiom, (
	![T]: (qualitytype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>quality(X)))))
)).

% Leaf nodes of the taxonomy of endurant types are disjoint 
%fof(endurantTypesDisjoint, conjecture, (
%	![X]: (substantialtype(X)=>(~relatortype(X)&~modetype(X)&~qualitytype(X))) &
%	![X]: (relatortype(X)=>(~substantialtype(X)&~modetype(X)&~qualitytype(X))) &
%	![X]: (modetype(X)=>(~substantialtype(X)&~relatortype(X)&~qualitytype(X))) &
%	![X]: (qualitytype(X)=>(~substantialtype(X)&~relatortype(X)&~modetype(X))) 
%)).

%%% Kinds are specialized according to the ontological nature of their instances

% Substantial kinds are those kinds whose instances are substantials
fof(dsubstantialKind, axiom, (
	![T]: (substantialkind(T)<=> (substantialtype(T) & kind(T)))
)).

% Relator kinds are those kinds whose instances are relators
fof(drelatorKind, axiom, (
	![T]: (relatorkind(T) <=> (relatortype(T) & kind(T))) 
)).

% Mode kinds are those kinds whose instances are modes
fof(dmodeKind, axiom, (
	![T]: (modekind(T)<=> (modetype(T) & kind(T)))
)).

% Quality kinds are those kinds whose instances are relators
fof(dqualityKind, axiom, (
	![T]: (qualitykind(T)<=> (qualitytype(T) & kind(T)))
)).

% Theorem
% if it is an instance of an endurant kind it must be an endurant
%fof(everyEndurant, conjecture, (
%	![X]: ((?[W,K]: ((substantialkind(K)|relatorkind(K)|modekind(K)|qualitykind(K))& iof(X,K,X)))=>endurant(X))
%)).

% every endurant is instance of one of the specific endurant kinds 
fof(everyEndurantInstantiatesSpecificKind, axiom, (
	![X]: (endurant(X) => (?[W,K]: ((substantialkind(K)|relatorkind(K)|modekind(K)|qualitykind(K))& iof(X,K,W))))
)).

% every endurant sortal is either a kinds, subkind, phase, role or semirigid sortal
%fof(categorizationEndurantSortalsComplete, conjecture, (
%	![X]: ((enduranttype(X)&sortal(X))=>(substantialkind(X)|relatorkind(X)|modekind(X)|qualitykind(X)|subkind(X)|phase(X)|role(X)|semirigidsortal(X))) 
%)).

% every endurant sortal specializes a specific kind
%fof(endurantSortalsSpecializeSpecificKinds, conjecture, (
%![T]: ((sortal(T)&(substantialtype(T)|relatortype(T)|modetype(T)|qualitytype(T)))<=>(?[K]: ((substantialkind(K)|relatorkind(K)|modekind(K)|qualitykind(K))&specializes(T,K))))
%)).

% leaves of the taxonomy of endurant types are disjoint
%fof(endurantTypesDisjoint, conjecture, (
%	![T]: (substantialkind(T)=>(~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
%	![T]: (subkind(T) => (~substantialkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
%	![T]: (relatorkind(T) => (~substantialkind(T)&~subkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
%	![T]: (modekind(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
%	![T]: (qualitykind(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
%	![T]: (category(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
%	![T]: (phase(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
%	![T]: (mixin(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
%	![T]: (role(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~phasemixin(T)&~rolemixin(T))) &
%	![T]: (phasemixin(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~rolemixin(T))) &
%	![T]: (rolemixin(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T))) 
%)).

% endurant types must be either kinds, subkind, phase, role, semirigid sortal, mixin, phasemixin and rolemixin
%fof(categorizationEndurantTypesComplete, conjecture, (
%	![X]: (enduranttype(X)=>(substantialkind(X)|relatorkind(X)|modekind(X)|qualitykind(X)|subkind(X)|phase(X)|role(X)|semirigidsortal(X)|category(X)|mixin(X)|phasemixin(X)|rolemixin(X))) 
%)).


%%% Theorems to show that we can omit <<relatorphase>> and <<relatorrole>> as a demonstration
% (same applies to relatorsubkind, modephase, moderole, modesubkind, qualityphase, qualityrole, qualitysubkind)

% Relator phase is a phase that is applicable to relators only
fof(drelatorPhase, axiom, (
	![T]: (relatorphase(T)<=> (relatortype(T) & phase(T)))
)).

% Theorem: if it is a phase and it specializes a relatorkind it is a relatorphase
%fof(relatorPhaseDerivation, conjecture, (
%    ![T]: (relatorphase(T) <=> (phase(T) & ?[K]: (relatorkind(K) & specializes(T,K))))
%)).

% Relator role is a role that is applicable to relators only
fof(drelatorRole, axiom, (
	![T]: (relatorrole(T)<=> (relatortype(T) & role(T)))
)).

% Theorem
% T is a RelatorRole iff it is a role and it specializes a relatorkind
%fof(relatorRoleDerivation, conjecture, (
%    ![T]: (relatorrole(T) <=> (role(T) & ?[K]: (relatorkind(K) & specializes(T,K))))
%)).

% Theorem: every sortal endurant type is one of the types we defined 
%(instances have the same ontological nature)
%fof(sameOntologicalNature, conjecture, (
%	![T]: ((sortal(T)&enduranttype(T))=>(relatortype(T)|substantialtype(T)|modetype(T)|qualitytype(T)))
%)).

% the same cannot be said for the nonsortals, so the following
% is *NOT* a theorem, as we would expect... it is independent of this theory
% this is because the nonsortals can have instances of the various ontological natures
%fof(sameOntologicalNature, conjecture, (
%	![T]: ((nonsortal(T)&enduranttype(T))=>(relatortype(T)|substantialtype(T)|modetype(T)|qualitytype(T)))
%)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fof(allTheorems, conjecture, (

	% about the domain of quantification
	![X]: (world(X)|type_(X)|individual(X)) &
	![X]: (world(X)=>(~type_(X)&~individual(X))) &
	~?[X]: (world(X)&type_(X)) &
	~?[X]: (world(X)&individual(X)) &
	~?[X]: (type_(X)&individual(X)) &

	% about specialization
	![X] : (type_(X)=>specializes(X,X)) &
	![X,Y,Z] : ((specializes(X,Y)&specializes(Y,Z))=>specializes(X,Z)) &		
	
	% about ridigity	
	![T]: (type_(T)<=>(rigid(T)|semirigid(T)|antirigid(T))) &
	~?[X]: ((rigid(X)&antirigid(X)) | (rigid(X)&semirigid(X)) | (semirigid(X)&antirigid(X))) &
	% about taxonomic relations and rigidity
	~?[X,Y]: (rigid(X)&antirigid(Y)&specializes(X,Y))  &
	~?[X,Y]: (semirigid(X)&antirigid(Y)&specializes(X,Y))  &
	
	% about sortality
	![T]: (kind(T)=>rigid(T)) &	
	![T] : (kind(T)=>sortal(T)) &
	![X,Y] : ( (kind(X)&kind(Y)&~(X=Y)) => (![W]: (world(W) => ~?[Z]:( iof(Z,X,W)&iof(Z,Y,W))))) &
	% about taxonomic relations and sortality
	![X] : (sortal(X)=>?[K]:(kind(K)&specializes(X,K)))  &
	~?[X,Y,Z]: (kind(Y)&kind(Z)&~(Y=Z)&specializes(X,Y)&specializes(X,Z)) &
	~?[X,Y]: (kind(X)&kind(Y)&~(X=X)&specializes(X,Y)) &
	~?[X,Y]: (nonsortal(X)&sortal(Y)&specializes(X,Y))  &	
	![T,X,W]: ((nonsortal(T) & iof(X,T,W)) =>
				((?[S]: (sortal(S)&specializes(S,T)&iof(X,S,W))) |
				(?[N,S]: (nonsortal(N)&sortal(S)&specializes(S,N)&specializes(T,N)&iof(X,S,W))))) &
				
	% about the leaf nodes in the taxonomy of types being disjoint and completely partitioning types
	![T]: (kind(T)=>(~subkind(T)&~role(T)&~phase(T)&~rolemixin(T)&~phasemixin(T)&~category(T)&~mixin(T))) &
	![T]: (subkind(T)=>(~kind(T)&~role(T)&~phase(T)&~rolemixin(T)&~phasemixin(T)&~category(T)&~mixin(T))) &
	![T]: (role(T)=>(~kind(T)&~subkind(T)&~phase(T)&~rolemixin(T)&~phasemixin(T)&~category(T)&~mixin(T))) &
	![T]: (phase(T)=>(~kind(T)&~subkind(T)&~role(T)&~rolemixin(T)&~phasemixin(T)&~category(T)&~mixin(T))) &
	![T]: (rolemixin(T)=>(~kind(T)&~subkind(T)&~role(T)&~phase(T)&~phasemixin(T)&~category(T)&~mixin(T))) &
	![T]: (phasemixin(T)=>(~kind(T)&~subkind(T)&~role(T)&~phase(T)&~rolemixin(T)&~category(T)&~mixin(T))) &
	![T]: (category(T)=>(~kind(T)&~subkind(T)&~role(T)&~phase(T)&~rolemixin(T)&~phasemixin(T)&~mixin(T))) &
	![T]: (mixin(T)=>(~kind(T)&~subkind(T)&~role(T)&~phase(T)&~rolemixin(T)&~phasemixin(T)&~category(T))) &
	![T]: (type_(T)<=>(kind(T)|subkind(T)|role(T)|phase(T)|semirigidsortal(T)|mixin(T)|rolemixin(T)|phasemixin(T)|category(T))) &
	
	% about the leaf nodes in the taxonomy of endurants being disjoint and completely partitioning endurant
	![X]: (substantial(X)=>(~relator(X)&~mode(X)&~quality(X))) &
	![X]: (relator(X)=>(~substantial(X)&~mode(X)&~quality(X))) &
	![X]: (mode(X)=>(~substantial(X)&~relator(X)&~quality(X))) &
	![X]: (quality(X)=>(~substantial(X)&~relator(X)&~mode(X))) &
	![X]: (endurant(X)<=>(substantial(X)|relator(X)|mode(X)|quality(X))) &
	
	% about the leaf nodes in the taxonomy of endurant types being disjoint
	![X]: (substantialtype(X)=>(~relatortype(X)&~modetype(X)&~qualitytype(X))) &
	![X]: (relatortype(X)=>(~substantialtype(X)&~modetype(X)&~qualitytype(X))) &
	![X]: (modetype(X)=>(~substantialtype(X)&~relatortype(X)&~qualitytype(X))) &
	![X]: (qualitytype(X)=>(~substantialtype(X)&~relatortype(X)&~modetype(X))) &
	% they are not a complete partition

	% disjointness of the leaves of the taxonomy of endurant kinds
	![T]: (substantialkind(T) => (~relatorkind(T)&~modekind(T)&~qualitykind(T))) &
	![T]: (relatorkind(T) => (~substantialkind(T)&~modekind(T)&~qualitykind(T))) &
	![T]: (modekind(T) => (~substantialkind(T)&~relatorkind(T)&~qualitykind(T))) &
	![T]: (qualitykind(T) => (~substantialkind(T)&~relatorkind(T)&~modekind(T))) 	&	
	% every endurant type that is a kind is one of substantialkind, relatorkind, modekind, qualitykind
	![T]: ((enduranttype(T)&kind(T))<=>(substantialkind(T)|relatorkind(T)|modekind(T)|qualitykind(T))) &

	% every endurant sortal specializes one of substantialkind, relatorkind, modekind(K), qualitykind(K)
	![T]: ((enduranttype(T)&sortal(T))=>(?[K]: ((substantialkind(K)|relatorkind(K)|modekind(K)|qualitykind(K))&(specializes(T,K))))) &

	% every endurant sortal is one of the kinds, subkind, phase, role or semirigid sortal
	![X]:  ((enduranttype(X)&sortal(X))=>
	              (substantialkind(X)|relatorkind(X)|modekind(X)|qualitykind(X)|subkind(X)|phase(X)|role(X)|semirigidsortal(X))) &

	% every endurant sortal specializes a specific kind
	![T]: ((sortal(T)&(substantialtype(T)|relatortype(T)|modetype(T)|qualitytype(T)))<=>(?[K]: ((substantialkind(K)|relatorkind(K)|modekind(K)|qualitykind(K))&specializes(T,K)))) &

	% leaves of the taxonomy of endurant types disjoint
	% pairwise disjointness
	![T]: (substantialkind(T)=>(~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
	![T]: (subkind(T) => (~substantialkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
	![T]: (relatorkind(T) => (~substantialkind(T)&~subkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
	![T]: (modekind(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
	![T]: (qualitykind(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
	![T]: (category(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
	![T]: (phase(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~mixin(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
	![T]: (mixin(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~role(T)&~phasemixin(T)&~rolemixin(T))) &
	![T]: (role(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~phasemixin(T)&~rolemixin(T))) &
	![T]: (phasemixin(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~rolemixin(T))) &
	![T]: (rolemixin(T) => (~substantialkind(T)&~subkind(T)&~relatorkind(T)&~modekind(T)&~qualitykind(T)&~category(T)&~phase(T)&~mixin(T)&~role(T)&~phasemixin(T))) &

	% endurant types must be either kinds, subkind, phase, role, semirigid sortal, mixin, phasemixin and rolemixin
	![X]: (enduranttype(X)=>
					(substantialkind(X)|relatorkind(X)|modekind(X)|qualitykind(X)|
					subkind(X)|phase(X)|role(X)|semirigidsortal(X)|category(X)|mixin(X)|phasemixin(X)|rolemixin(X))) & 

	
	% just a sample to show we can omit specific sorts of relator types
    ![T]: (relatorphase(T) <=> (phase(T) & ?[K]: (relatorkind(K) & specializes(T,K)))) &
    ![T]: (relatorrole(T) <=> (role(T) & ?[K]: (relatorkind(K) & specializes(T,K))))  &

	% sortal endurant types are "uniform", i.e., their instances are all of the same ontological nature	
	![T]: ((sortal(T)&enduranttype(T))=>(relatortype(T)|substantialtype(T)|modetype(T)|qualitytype(T))) 

)).
