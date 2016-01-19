package org.protege.owl.codegeneration.inference;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.protege.owl.codegeneration.names.CodeGenerationNames;
import org.protege.owl.codegeneration.property.JavaDataPropertyDeclaration;
import org.protege.owl.codegeneration.property.JavaObjectPropertyDeclaration;
import org.protege.owl.codegeneration.property.JavaPropertyDeclaration;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLDataRange;
import org.semanticweb.owlapi.model.OWLDatatype;
import org.semanticweb.owlapi.model.OWLDatatypeRestriction;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLOntology;

public class SimpleInference implements CodeGenerationInference {
	private OWLOntology ontology;
	private OWLDataFactory factory;
	private Set<OWLClass> topLevelClasses;
	private Map<OWLClass, Set<OWLClass>> inferredSubclassMap = new TreeMap<OWLClass, Set<OWLClass>>();
	private Map<OWLClass, Set<OWLClass>> indirectSuperclassMap = new HashMap<OWLClass, Set<OWLClass>>();
	private Map<OWLClass, Set<OWLEntity>> domainMap;
	private Map<OWLObjectProperty, OWLClass> objectRangeMap;
	private Map<OWLDataProperty, OWLDatatype> dataRangeMap;

	public SimpleInference(OWLOntology ontology) {
		this.ontology = ontology;
		this.factory = ontology.getOWLOntologyManager().getOWLDataFactory();
	}

	public OWLOntology getOWLOntology() {
		return this.ontology;
	}

	public void preCompute() {
		;
	}

	public void flush() {
		;
	}

	public Collection<OWLClass> getOwlClasses() {
		Set<OWLClass> classes = new HashSet<OWLClass>(this.ontology.getClassesInSignature());
		classes.remove(this.factory.getOWLThing());
		return classes;
	}

	public Collection<OWLClass> getSubClasses(OWLClass owlClass) {
		if (this.topLevelClasses == null) {
			this.initializeInferredSubclasses();
		}
		if (owlClass.equals(this.factory.getOWLThing())) {
			return Collections.unmodifiableCollection(this.topLevelClasses);
		} else {
			Set<OWLClass> subClasses = new TreeSet<OWLClass>();
			for (OWLClassExpression ce : owlClass.getSubClasses(this.ontology)) {
				if (!ce.isAnonymous()) {
					subClasses.add(ce.asOWLClass());
				}
			}
			Set<OWLClass> inferredSubclasses = this.inferredSubclassMap.get(owlClass);
			if (inferredSubclasses != null) {
				subClasses.addAll(inferredSubclasses);
			}
			return subClasses;
		}
	}

	public Collection<OWLClass> getSuperClasses(OWLClass owlClass) {
		Set<OWLClass> superClasses = new HashSet<OWLClass>();
		for (OWLClassExpression ce : owlClass.getSuperClasses(this.ontology.getImportsClosure())) {
			if (!ce.isAnonymous()) {
				superClasses.add(ce.asOWLClass());
			} else if (ce instanceof OWLObjectIntersectionOf) {
				superClasses.addAll(this.getNamedConjuncts((OWLObjectIntersectionOf) ce));
			}
		}
		for (OWLClassExpression ce : owlClass.getEquivalentClasses(this.ontology.getImportsClosure())) {
			if (ce instanceof OWLObjectIntersectionOf) {
				superClasses.addAll(this.getNamedConjuncts((OWLObjectIntersectionOf) ce));
			}
		}
		superClasses.remove(this.factory.getOWLThing());
		return superClasses;
	}

	private Collection<OWLClass> getNamedConjuncts(OWLObjectIntersectionOf ce) {
		Set<OWLClass> conjuncts = new HashSet<OWLClass>();
		for (OWLClassExpression conjunct : ce.getOperands()) {
			if (!conjunct.isAnonymous()) {
				conjuncts.add(conjunct.asOWLClass());
			}
		}
		return conjuncts;
	}

	public Collection<OWLNamedIndividual> getPropertyValues(OWLNamedIndividual i, OWLObjectProperty p) {
		Collection<OWLNamedIndividual> results = new HashSet<OWLNamedIndividual>();
		for (OWLOntology imported : this.ontology.getImportsClosure()) {
			for (OWLIndividual j : i.getObjectPropertyValues(p, imported)) {
				if (!j.isAnonymous()) {
					results.add(j.asOWLNamedIndividual());
				}
			}
		}
		return results;
	}

	public Collection<OWLLiteral> getPropertyValues(OWLNamedIndividual i, OWLDataProperty p) {
		Set<OWLLiteral> results = new HashSet<OWLLiteral>();
		for (OWLOntology imported : this.ontology.getImportsClosure()) {
			results.addAll(i.getDataPropertyValues(p, imported));
		}
		return results;
	}

	public Set<JavaPropertyDeclaration> getJavaPropertyDeclarations(OWLClass cls, CodeGenerationNames names) {
		if (this.domainMap == null) {
			this.initializeDomainMap();
		}
		Set<JavaPropertyDeclaration> declarations = new HashSet<JavaPropertyDeclaration>();
		Set<OWLEntity> domains = this.domainMap.get(cls);
		if (domains != null) {
			for (OWLEntity property : domains) {
				if (property instanceof OWLObjectProperty) {
					declarations.add(new JavaObjectPropertyDeclaration(this, names, (OWLObjectProperty) property));
				} else {
					declarations.add(new JavaDataPropertyDeclaration(this, cls, (OWLDataProperty) property));
				}
			}
		}
		return declarations;
	}

	public boolean isFunctional(OWLObjectProperty p) {
		OWLAxiom functionalAxiom = this.factory.getOWLFunctionalObjectPropertyAxiom(p);
		return this.ontology.containsAxiomIgnoreAnnotations(functionalAxiom);
	}

	public OWLClass getRange(OWLObjectProperty p) {
		if (this.objectRangeMap == null) {
			this.intializeObjectRangeMap();
		}
		return this.objectRangeMap.get(p);
	}

	public OWLClass getRange(OWLClass owlClass, OWLObjectProperty p) {
		return this.getRange(p);
	}

	public boolean isFunctional(OWLDataProperty p) {
		OWLAxiom functionalAxiom = this.factory.getOWLFunctionalDataPropertyAxiom(p);
		return this.ontology.containsAxiomIgnoreAnnotations(functionalAxiom);
	}

	public OWLDatatype getRange(OWLDataProperty p) {
		if (this.dataRangeMap == null) {
			this.intializeDataRangeMap();
		}
		return this.dataRangeMap.get(p);
	}

	public OWLDatatype getRange(OWLClass owlClass, OWLDataProperty p) {
		return this.getRange(p);
	}

	public Collection<OWLNamedIndividual> getIndividuals(OWLClass owlClass) {
		Set<OWLNamedIndividual> individuals = new HashSet<OWLNamedIndividual>();
		for (OWLIndividual i : owlClass.getIndividuals(this.ontology)) {
			if (!i.isAnonymous()) {
				individuals.add(i.asOWLNamedIndividual());
			}
		}
		return individuals;
	}

	public boolean canAs(OWLNamedIndividual i, OWLClass c) {
		Collection<OWLClass> types = this.getTypes(i);
		if (types.contains(c)) {
			return true;
		}
		for (OWLClass type : types) {
			if (this.getIndirectSuperClasses(type).contains(c)) {
				return true;
			}
		}
		return false;
	}

	public Collection<OWLClass> getTypes(OWLNamedIndividual i) {
		Set<OWLClass> types = new HashSet<OWLClass>();
		for (OWLClassExpression ce : i.getTypes(this.ontology.getImportsClosure())) {
			if (!ce.isAnonymous()) {
				types.add(ce.asOWLClass());
			}
		}
		return types;
	}

	/*
	 *  *-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
	 * *-*-*-*-*-*-*-*-*
	 */

	private void initializeInferredSubclasses() {
		this.topLevelClasses = new TreeSet<OWLClass>();
		for (OWLClass owlClass : this.ontology.getClassesInSignature()) {
			boolean foundParent = false;
			for (OWLClassExpression parent : owlClass.getSuperClasses(this.ontology)) {
				if (this.hasGoodDirectSuperClass(owlClass, parent) || this.searchForSuperclassesFromIntersection(owlClass, parent)) {
					foundParent = true;
				}
			}
			for (OWLClassExpression parent : owlClass.getEquivalentClasses(this.ontology)) {
				if (this.searchForSuperclassesFromIntersection(owlClass, parent)) {
					foundParent = true;
				}
			}
			if (!foundParent) {
				this.topLevelClasses.add(owlClass);
			}
		}
	 }

	private boolean hasGoodDirectSuperClass(OWLClass child, OWLClassExpression parent) {
		 return !parent.isAnonymous() && !parent.equals(this.factory.getOWLThing());
	 }

	 private boolean searchForSuperclassesFromIntersection(OWLClass child, OWLClassExpression parent) {
		 if (parent instanceof OWLObjectIntersectionOf) {
			 for (OWLClassExpression conjunct : ((OWLObjectIntersectionOf) parent).getOperands()) {
				 if (!conjunct.isAnonymous() && !conjunct.equals(this.factory.getOWLThing())) {
					 Set<OWLClass> inferredSubclasses = this.inferredSubclassMap.get(conjunct);
					 if (inferredSubclasses == null) {
						 inferredSubclasses = new TreeSet<OWLClass>();
						 this.inferredSubclassMap.put(conjunct.asOWLClass(), inferredSubclasses);
					 }
					 inferredSubclasses.add(child);
					 return true;
				 }
			 }
		 }
		 return false;
	 }

	private void initializeDomainMap() {
		 this.domainMap = new HashMap<OWLClass, Set<OWLEntity>>();
		 for (OWLObjectPropertyDomainAxiom axiom : this.ontology.getAxioms(AxiomType.OBJECT_PROPERTY_DOMAIN)) {
			 if (!axiom.getDomain().isAnonymous() && !axiom.getProperty().isAnonymous()) {
				 OWLClass owlClass = axiom.getDomain().asOWLClass();
				 Set<OWLEntity> domains = this.domainMap.get(owlClass);
				 if (domains == null) {
					 domains = new HashSet<OWLEntity>();
					 this.domainMap.put(owlClass, domains);
				 }
				 domains.add(axiom.getProperty().asOWLObjectProperty());
			 }
		 }
		 for (OWLDataPropertyDomainAxiom axiom : this.ontology.getAxioms(AxiomType.DATA_PROPERTY_DOMAIN)) {
			 if (!axiom.getDomain().isAnonymous() && !axiom.getProperty().isAnonymous()) {
				 OWLClass owlClass = axiom.getDomain().asOWLClass();
				 Set<OWLEntity> domains = this.domainMap.get(owlClass);
				 if (domains == null) {
					 domains = new HashSet<OWLEntity>();
					 this.domainMap.put(owlClass, domains);
				 }
				 domains.add(axiom.getProperty().asOWLDataProperty());
			 }
		 }
	 }

	private void intializeObjectRangeMap() {
		 this.objectRangeMap = new HashMap<OWLObjectProperty, OWLClass>();
		 for (OWLObjectPropertyRangeAxiom axiom : this.ontology.getAxioms(AxiomType.OBJECT_PROPERTY_RANGE)) {
			 if (!axiom.getRange().isAnonymous() && !axiom.getProperty().isAnonymous()) {
				 OWLObjectProperty property = axiom.getProperty().asOWLObjectProperty();
				 if (this.objectRangeMap.get(property) == null) {
					 this.objectRangeMap.put(property, axiom.getRange().asOWLClass());
				 }
			 }
		 }
	 }

	private void intializeDataRangeMap() {
		 this.dataRangeMap = new HashMap<OWLDataProperty, OWLDatatype>();
		 for (OWLDataPropertyRangeAxiom axiom : this.ontology.getAxioms(AxiomType.DATA_PROPERTY_RANGE)) {
			 if (!axiom.getProperty().isAnonymous()) {
				 OWLDataProperty property = axiom.getProperty().asOWLDataProperty();
				 OWLDatatype dt = this.getContainingDatatype(axiom.getRange());
				 if (this.dataRangeMap.get(property) == null && dt != null) {
					 this.dataRangeMap.put(property, dt);
				 }
			 }
		 }
	 }

	private OWLDatatype getContainingDatatype(OWLDataRange range) {
		 if (range instanceof OWLDatatype) {
			 return (OWLDatatype) range;
		 } else if (range instanceof OWLDatatypeRestriction) {
			 return ((OWLDatatypeRestriction) range).getDatatype();
		 }
		 return null;
	 }

	private Set<OWLClass> getIndirectSuperClasses(OWLClass cls) {
		Set<OWLClass> superClasses = this.indirectSuperclassMap.get(cls);
		if (superClasses == null) {
			superClasses = new HashSet<OWLClass>();
			this.addIndirectSuperClasses(superClasses, cls);
			this.indirectSuperclassMap.put(cls, superClasses);
		}
		return superClasses;
	 }

	private void addIndirectSuperClasses(Set<OWLClass> superClasses, OWLClass cls) {
		Collection<OWLClass> newSuperClasses = this.getSuperClasses(cls);
		newSuperClasses.removeAll(superClasses);
		superClasses.addAll(newSuperClasses);
		for (OWLClass newSuperClass : newSuperClasses) {
			this.addIndirectSuperClasses(superClasses, newSuperClass);
		}
	 }

}
