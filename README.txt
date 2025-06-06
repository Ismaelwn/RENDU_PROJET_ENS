Voici le texte corrigé avec les caractères superflus retirés (`*`, `**`, etc.), sans suppression de contenu, et avec une **conclusion ajoutée** :

---

**Introduction :**

Le présent rapport décrit la conception et l’implémentation d’un borrow checker pour MiniRust, un sous-ensemble idéalisé du langage Rust, dans le cadre du cours de Programmation Avancée de l’ENS Paris-Saclay. Le borrow checker est un composant fondamental du compilateur Rust chargé d’assurer la sûreté mémoire : il garantit qu’aucune donnée n’est lue ou modifiée via des pointeurs invalides ou simultanément mutés et partagés. Si un programme est accepté à la fois par le vérificateur de types et par le borrow checker, il ne peut produire aucun comportement indéfini.

Nous ciblons ici MiniRust, un langage simplifié proposant :

* les types de base (`i32`, `()`, structures) ;
* les emprunts partagés et mutables, avec inférence de durées de vie pour les variables locales ;
* une représentation intermédiaire MiniMir à base de graphe de flot de contrôle, générée automatiquement par le front-end fourni.

Le projet se décompose en cinq tâches principales :

1. l’analyse d’initialisation des « places » (zones mémoire accessibles) et la détection d’usages non initialisés,
2. la vérification des conflits d’emprunts mutables et partagés,
3. la génération et la résolution des contraintes de durées de vie,
4. la validation des contraintes de sous-typage de durée de vie génériques,
5. l’émission d’erreurs sur les opérations interdites quand des emprunts actifs entrent en conflit.

Après avoir présenté l’architecture générale de MiniRust et le fonctionnement attendu du borrow checker, ce rapport détaille les choix de conception, les algorithmes mis en œuvre et les difficultés rencontrées. Il se conclut sur une évaluation des tests fonctionnels réalisés et propose des axes d’extension pour aller au-delà du périmètre initial.

---

**uninitialized\_places.ml :**

Dans `uninitialized_places.ml`, plusieurs modules et fonctions se combinent pour réaliser l’analyse des « places » non initialisées, conformément à la première tâche du projet :
Le cœur du travail réalisé se concentre sur la première tâche du projet : l’analyse statique d’initialisation des places dans `uninitialized_places.ml`.
Voici, en détail, ce qui a été implémenté et pourquoi :

* Pré-calcul des places et de leur hiérarchie
  Nous générons d’abord l’ensemble exhaustif des places qui apparaissent dans le MiniMir de la fonction, puis nous construisons pour chacune la fermeture par sous-place. Cela permet, plus loin, de (dés)initialiser récursivement une structure complète d’un simple appel, condition indispensable pour refléter la sémantique Rust : lorsqu’un champ est déplacé, le reste de la structure devient partiellement non initialisé.

* Fonctions `initialize`, `deinitialize` et nouveau `move_or_copy`
  `initialize` / `deinitialize` appliquent ces fermetures pour ajouter ou retirer les sous-places pertinentes de l’ensemble abstrait « non initialisé ».
  `move_or_copy` a été réécrit : il distingue désormais la copie d’une valeur `Copy` (qui laisse la source intacte) du move d’une valeur non-`Copy` (qui ajoute la place et toutes ses sous-places à l’état « non initialisé »). Cette distinction est cruciale pour que le borrow checker interdise uniquement les lectures fautives.

* Module `Graph` (interface pour l’algorithme de point fixe `Fix`)
  `foreach_root` instancie la racine du flot de contrôle avec l’état dans lequel toutes les places locales sont non initialisées – hypothèse de départ imposée par le modèle mémoire MiniRust.
  `foreach_successor` encode l’effet précis de chaque instruction MiniMir :

  * consommation de paramètres à l’entrée d’un bloc,
  * propagation de l’état vers chaque successeur du graphe,
  * appels à `initialize`, `deinitialize` ou `move_or_copy` selon qu’une instruction écrit, lit ou déplace une place.

Cette implémentation complète la chaîne attendue par le foncteur `Fix.DataFlow.ForIntSegment`, permettant de résoudre le système d’équations de flot de données et d’associer à chaque étiquette de code l’ensemble exact des places potentiellement non initialisées.

Grâce à ces ajouts, l’analyse fournit maintenant les informations requises par `borrowck.ml` pour émettre les erreurs « use of possibly-uninitialized » et « use of moved value », conformément au comportement de Rust, et valide donc intégralement la première étape imposée par le sujet.

---

**borrowck.ml :**

Dans `borrowck.ml`, plusieurs blocs de code ont été ajoutés pour prendre en charge la vérification des emprunts et des durées de vie, en complément de l’analyse d’initialisation :

* Génération des contraintes de durées de vie
  La fonction `compute_lft_sets` initialise une table `outlives` à partir des types des variables locales (via `implied_outlives prog typ`) puis enrichit cette table en parcourant explicitement chaque instruction pour :

  1. Unifier les lifetimes lorsque deux références doivent être identiques (`unify_lft`).
  2. Ajouter des arêtes d’outlives pour les appels de fonction (à l’aide de `fn_prototype_fresh`) et pour les reborrows lorsqu’un emprunt est fait sur une valeur déjà empruntée (en comparant les niveaux de déréférencement).
     Parallèlement, la table `living` collecte, pour chaque point de programme, les lifetimes qui doivent être « vivants » :

     * Tous les lifetimes libres dans le type des variables encore vivantes (`live_locals`) sont marqués comme tels.
     * Les lifetimes génériques (`mir.mgeneric_lfts`) sont contraints d’être vivants dès le point `PpInCaller`.

  Enfin, on résout ces deux ensembles de contraintes en point fixe avec le module `Fix.Fix.ForType`, produisant pour chaque lifetime l’ensemble des points de programme où elle doit subsister.

* Vérification des emprunts dans `borrowck`

  1. Initialisation : on réutilise le résultat d’`Uninitialized_places.go` pour interdire tout accès en lecture ou écriture sur une place non initialisée (`check_initialized`).
  2. Immutabilité des emprunts partagés : un scan supplémentaire (à compléter) doit empêcher toute écriture sous une référence partagée — la fonction utilitaire `place_mut` permet déjà de détecter si un emplacement désigne un emprunt mutable ou non.
  3. Conflits d’emprunt :

     * On invoque `Active_borrows.go prog lft_sets mir` pour obtenir, à chaque label, la liste des emprunts encore actifs.
     * La fonction `conflicting_borrow_no_deref` couvre les écritures qui modifient directement un emplacement emprunté (même sans déréférencer), et `conflicting_borrow` étend la détection aux lectures/écritures mixtes en comparant places et sous-places avec le niveau de mutabilité (`Mut`).
     * Le cas général d’« usage » (`check_use`) interdit également de déplacer (`move`) ou copier une valeur hors d’un emprunt (`contains_deref_borrow`).
  4. Cas particuliers : les instructions `Ideinit` et `Ireturn` reçoivent un traitement spécifique pour s’assurer qu’aucune variable ne sort de portée alors qu’elle est encore empruntée, ou qu’aucun paramètre retourné ne soit toujours référencé.

Ces ajouts mettent en œuvre, dans un style strictement modulaire, la tâche de vérification des emprunts : génération des contraintes de durée de vie, propagation par point fixe, et détection systématique des conflits lecture/écriture avec les emprunts actifs.

---

**Problèmes :**

Cependant, notre implémentation n'est pas complète car deux tests, pour des raisons qui m'échappent, ne passent pas malgré le travail réalisé.

Le fichier `67.rs` vérifie la bonne gestion des contraintes entre lifetimes génériques.
Dans la fonction `g<'a, 'b>`, le type de retour annoncé est `&'b i32`, alors que la valeur réellement renvoyée – la variable `t` – a le type `&'a i32`. Pour que ce code soit accepté, il faudrait qu’une contrainte explicite déclare que `'a` vit au moins aussi longtemps que `'b` ; or rien de tel n’apparaît dans la signature. Le test devrait donc retourner une erreur, cependant notre implémentation n'en provoque pas. Le problème est identifié ; la difficulté a été d’essayer de le corriger, chose que je n'ai pas réussi à faire.
L’erreur que doit émettre la tâche 4 serait quelque chose du genre : « vérifier que toutes les relations *out-lives* nécessaires entre paramètres génériques figurent bien dans le prototype de la fonction ».

Le fichier `70.rs`, lui, met à l’épreuve la génération même des contraintes *out-lives*.
La fonction `f` attend deux paramètres de type `&'o mut &'a mut i32` ; lors de l’appel dans `g`, on passe `&mut x` (ok) puis `&mut b`, où `b` est un emprunt mutable créé juste avant sur une variable locale `y`.
Pour que l’appel soit sûr, le borrow checker doit conclure que l’emprunt interne porté par `b` possède – comme celui de `x` – la lifetime `'a`. Or la règle des reborrows impose au contraire que ce nouvel emprunt soit plus court, puisque la source (`y`) ne survit pas aussi longtemps que `'a`. Le test s’assure que l’analyse ajoute bien la contrainte « lifetime du nouveau borrow < 'a » et qu’elle détecte l’incompatibilité lors de l’appel. Il cible donc directement la tâche 3. Pareil ici, aucune erreur n’est déclenchée.

---

**Extension :**

Dans ce projet, je n'ai implémenté aucune extension étant donné que deux tests ne passaient pas. J’ai voulu concentrer mon temps dessus. Malheureusement, je n’ai pas réussi à les faire fonctionner.

---

**Conclusion :**

La conception du borrow checker pour MiniRust a permis de mettre en œuvre les fondements de la sûreté mémoire dans un langage à emprunts inspiré de Rust. Le projet a abouti à une implémentation fonctionnelle de l’analyse d’initialisation, de la vérification des emprunts et de la gestion des durées de vie via des contraintes de type `outlives`.
Malgré des progrès significatifs et une architecture modulaire cohérente, deux cas limites n’ont pas pu être résolus. Ils illustrent les défis que pose la gestion fine des relations entre durées de vie génériques, en particulier dans un contexte d'inférence automatique.
Cette expérience m’a permis de mieux comprendre les subtilités du système de prêt de Rust, mais aussi la difficulté de garantir statiquement l’absence d’erreurs dans un système riche en contraintes implicites. Ces deux échecs partiels constituent des pistes claires de travail futur pour une implémentation pleinement conforme au modèle Rust.
