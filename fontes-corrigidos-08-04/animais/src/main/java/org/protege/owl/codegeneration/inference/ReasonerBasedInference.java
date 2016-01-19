package org.protege.owl.codegeneration.inference;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.apache.log4j.Logger;
import org.protege.owl.codegeneration.HandledDatatypes;
import org.protege.owl.codegeneration.names.CodeGenerationNames;
import org.protege.owl.codegeneration.property.JavaDataPropertyDeclaration;
import org.protege.owl.codegeneration.property.JavaObjectPropertyDeclaration;
import org.protege.owl.codegeneration.property.JavaPropertyDeclaration;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDatatype;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

public class ReasonerBasedInference implements CodeGenerationInference {
	public static final Logger LOGGER = Logger.getLogger(ReasonerBasedInference.class);

	private OWLOntology ontology;
	private OWLReasoner reasoner;
	private OWLDataFactory factory;
	private Set<OWLClass> allClasses;
	private Map<OWLClass, Set<OWLEntity>> domainMap;
	private Map<OWLClass, Map<OWLObjectProperty, OWLClass>> objectRangeMap = new HashMap<OWLClass, Map<OWLObjectProperty, OWLClass>>();
	private Map<OWLClass, Map<OWLDataProperty, OWLDatatype>> dataRangeMap = new HashMap<OWLClass, Map<OWLDataProperty, OWLDatatype>>();

	public ReasonerBasedInference(OWLOntology ontology, OWLReasoner reasoner) {
		this.ontology = ontology;
		this.reasoner = reasoner;
		this.factory = ontology.getOWLOntologyManager().getOWLDataFactory();
	}

	public OWLOntology getOWLOntology() {
		return this.ontology;
	}

	public void preCompute() {
		this.reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS);
	}

	public void flush() {
		this.reasoner.flush();
	}

	public Collection<OWLClass> getOwlClasses() {
		if (this.allClasses == null) {
			this.allClasses = new HashSet<OWLClass>(this.ontology.getClassesInSignature());
			this.allClasses.removeAll(this.reasoner.getUnsatisfiableClasses().getEntities());
			this.allClasses.removeAll(this.reasoner.getEquivalentClasses(this.factory.getOWLThing()).getEntities());
		}
		return this.allClasses;
	}

	public Collection<OWLClass> getSubClasses(OWLClass owlClass) {
		return this.reasoner.getSubClasses(owlClass, true).getFlattened();
	}

	public Collection<OWLClass> getSuperClasses(OWLClass owlClass) {
		return this.reasoner.getSuperClasses(owlClass, true).getFlattened();
	}

	public Set<JavaPropertyDeclaration> getJavaPropertyDeclarations(OWLClass cls, CodeGenerationNames names) {
		if (this.domainMap == null) {
			this.initializeDomainMap();
		}
		Set<JavaPropertyDeclaration> declarations = new HashSet<JavaPropertyDeclaration>();
		if (this.domainMap.get(cls) != null) {
			for (OWLEntity p : this.domainMap.get(cls)) {
				if (p instanceof OWLObjectProperty) {
					declarations.add(new JavaObjectPropertyDeclaration(this, names, (OWLObjectProperty) p));
				} else if (p instanceof OWLDataProperty) {
					declarations.add(new JavaDataPropertyDeclaration(this, cls, (OWLDataProperty) p));
				}
			}
		}
		return declarations;
	}

	public boolean isFunctional(OWLObjectProperty p) {
		OWLClassExpression moreThanTwoValues = this.factory.getOWLObjectMinCardinality(2, p);
		return !this.reasoner.isSatisfiable(moreThanTwoValues);
	}

	public OWLClass getRange(OWLObjectProperty p) {
		return this.getRange(this.factory.getOWLThing(), p);
	}

	public OWLClass getRange(OWLClass owlClass, OWLObjectProperty p) {
		Map<OWLObjectProperty, OWLClass> property2RangeMap = this.objectRangeMap.get(owlClass);
		if (property2RangeMap == null) {
			property2RangeMap = new HashMap<OWLObjectProperty, OWLClass>();
			this.objectRangeMap.put(owlClass, property2RangeMap);
		}
		OWLClass cls = property2RangeMap.get(p);
		if (cls == null) {
			OWLClassExpression possibleValues = this.factory.getOWLObjectSomeValuesFrom(this.factory.getOWLObjectInverseOf(p), owlClass);
			Collection<OWLClass> classes;
			classes = this.reasoner.getEquivalentClasses(possibleValues).getEntities();
			if (classes != null && !classes.isEmpty()) {
				cls = asSingleton(classes, this.ontology);
			} else {
				classes = this.reasoner.getSuperClasses(possibleValues, true).getFlattened();
				cls = asSingleton(classes, this.ontology);
			}
			property2RangeMap.put(p, cls);
		}
		return cls;
	}

	public boolean isFunctional(OWLDataProperty p) {
		OWLClassExpression moreThanTwoValues = this.factory.getOWLDataMinCardinality(2, p);
		return !this.reasoner.isSatisfiable(moreThanTwoValues);
	}

	public OWLDatatype getRange(OWLDataProperty p) {
		return this.getRange(this.factory.getOWLThing(), p);
	}

	public OWLDatatype getRange(OWLClass owlClass, OWLDataProperty p) {
		Map<OWLDataProperty, OWLDatatype> property2RangeMap = this.dataRangeMap.get(owlClass);
		if (property2RangeMap == null) {
			property2RangeMap = new HashMap<OWLDataProperty, OWLDatatype>();
			this.dataRangeMap.put(owlClass, property2RangeMap);
		}
		OWLDatatype range = property2RangeMap.get(p);
		if (range == null) {
			for (HandledDatatypes handled : HandledDatatypes.values()) {
				OWLDatatype dt = this.factory.getOWLDatatype(handled.getIri());
				OWLClassExpression couldHaveOtherValues = this.factory.getOWLObjectComplementOf(this.factory.getOWLDataAllValuesFrom(p, dt));
				OWLClassExpression classCouldHaveOtherValues = this.factory.getOWLObjectIntersectionOf(owlClass, couldHaveOtherValues);
				if (!this.reasoner.isSatisfiable(classCouldHaveOtherValues)) {
					range = dt;
					break;
				}
			}
			if (range != null) {
				property2RangeMap.put(p, range);
			}
		}
		return range;
	}

	public Collection<OWLNamedIndividual> getIndividuals(OWLClass owlClass) {
		return this.reasoner.getInstances(owlClass, false).getFlattened();
	}

	public boolean canAs(OWLNamedIndividual i, OWLClass c) {
		OWLDataFactory factory = this.ontology.getOWLOntologyManager().getOWLDataFactory();
		return this.reasoner.isSatisfiable(factory.getOWLObjectIntersectionOf(c, factory.getOWLObjectOneOf(i)));
	}

	public Collection<OWLClass> getTypes(OWLNamedIndividual i) {
		return this.reasoner.getTypes(i, true).getFlattened();
	}

	public Collection<OWLNamedIndividual> getPropertyValues(OWLNamedIndividual i, OWLObjectProperty p) {
		return this.reasoner.getObjectPropertyValues(i, p).getFlattened();
	}

	public Collection<OWLLiteral> getPropertyValues(OWLNamedIndividual i, OWLDataProperty p) {
		Set<OWLLiteral> results = new HashSet<OWLLiteral>();
		results.addAll(this.reasoner.getDataPropertyValues(i, p));
		// the behavior of getDataPropertyValues is somewhat undefined
		// so make sure that the asserted ones are included.
		for (OWLOntology imported : this.ontology.getImportsClosure()) {
			results.addAll(i.getDataPropertyValues(p, imported));
		}
		return results;
	}

	/*
	 * *-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-*-
	 * *-*-*-*-*-*-*-*-*
	 */
	private static <X extends OWLEntity> X asSingleton(Collection<X> xs, OWLOntology owlOntology) {
		X result = null;
		for (X x : xs) {
			if (owlOntology.containsEntityInSignature(x, true)) {
				if (result == null) {
					result = x;
				} else {
					return null;
				}
			}
		}
		return result;
	}

	private void initializeDomainMap() {
		this.domainMap = new HashMap<OWLClass, Set<OWLEntity>>();
		for (OWLObjectProperty p : this.ontology.getObjectPropertiesInSignature()) {
			OWLClassExpression mustHavePropertyValue = this.factory.getOWLObjectSomeValuesFrom(p, this.factory.getOWLThing());
			this.addPropertyToDomainMap(p, mustHavePropertyValue);
		}
		for (OWLDataProperty p : this.ontology.getDataPropertiesInSignature()) {
			OWLClassExpression mustHavePropertyValue = this.factory.getOWLDataSomeValuesFrom(p, this.factory.getTopDatatype());
			this.addPropertyToDomainMap(p, mustHavePropertyValue);
		}
	}

	private void addPropertyToDomainMap(OWLEntity p, OWLClassExpression mustHavePropertyValue) {
		Set<OWLClass> equivalents = this.reasoner.getEquivalentClasses(mustHavePropertyValue).getEntities();
		if (!equivalents.isEmpty()) {
			for (OWLClass domain : equivalents) {
				this.addToDomainMap(domain, p);
			}
		} else {
			for (OWLClass domain : this.reasoner.getSuperClasses(mustHavePropertyValue, true).getFlattened()) {
				this.addToDomainMap(domain, p);
			}
		}
	}

	private void addToDomainMap(OWLClass domain, OWLEntity property) {
		Set<OWLEntity> properties = this.domainMap.get(domain);
		if (properties == null) {
			properties = new TreeSet<OWLEntity>();
			this.domainMap.put(domain, properties);
		}
		properties.add(property);
	}

}
