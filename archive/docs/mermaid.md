graph TD
    %% --- Styling Definitions ---
    classDef core fill:#e1f5fe,stroke:#01579b,stroke-width:2px;
    classDef engine fill:#d4edda,stroke:#28a745,stroke-width:2px;
    classDef interface fill:#e8eaf6,stroke:#3f51b5,stroke-width:2px,stroke-dasharray: 5 5;
    classDef p1 fill:#f0f4c3,stroke:#827717,stroke-width:2px;
    classDef elliptic fill:#fff3cd,stroke:#ffc107,stroke-width:2px;
    classDef axiom fill:#ffebee,stroke:#c62828,stroke-width:2px,stroke-dasharray: 5 5;
    classDef todo fill:#f5f5f5,stroke:#9e9e9e,stroke-width:2px,stroke-dasharray: 2 2;

    %% --- Layer 1: The Core Kernel (Verified) ---
    subgraph Core_Infrastructure ["Layer 1: Core Kernel (Curve Agnostic)"]
        direction TB
        Core_Place["Core/Place.lean"]:::core
        Core_Divisor["Core/Divisor.lean"]:::core
        Core_RRSpace["Core/RRSpace.lean"]:::core
        
        Core_Place --> Core_Divisor
        Core_Divisor --> Core_RRSpace
    end

    %% --- Layer 2: The Adelic Engine ---
    subgraph Adelic_Engine ["Layer 2: The Adelic Engine"]
        direction TB
        Adelic_Topology["Adelic/AdelicTopology.lean"]:::engine
        Adelic_H1["Adelic/AdelicH1v2.lean"]:::engine
        Residue_Theory["ResidueTheory/ResidueTheorem.lean"]:::engine
        
        %% The Strong Approximation Hub
        StrongApprox["Adelic/StrongApproximation.lean<br/>(Cycle 291: Topological Density)"]:::engine
        
        %% The "Slop" that needs fixing in Cycle 295
        AdelicH1Full["AdelicH1Full.lean<br/>(Contains Infinity Bound Sorries)"]:::todo

        Core_RRSpace --> Adelic_H1
        Adelic_Topology --> StrongApprox
        Adelic_Topology --> AdelicH1Full
    end

    %% --- Layer 3: Serre Duality & Interface ---
    subgraph Logic_Layer ["Layer 3: Abstract Logic"]
        Serre_Abstract["SerreDuality/Abstract.lean"]:::engine
        RRData_Class["Definitions/ProjectiveAdelicRRData<br/>(The Interface Typeclass)"]:::interface

        Adelic_H1 --> Serre_Abstract
        AdelicH1Full -.-> Serre_Abstract
        Residue_Theory --> Serre_Abstract
        Serre_Abstract --> RRData_Class
    end

    %% --- Layer 4a: P1 Instance (Completed) ---
    subgraph P1_Implementation ["Layer 4a: Genus 0 (P¹)"]
        P1_Poly["P1Instance/FqPolynomialInstance.lean"]:::p1
        P1_Proof["P1Instance/P1RiemannRoch.lean"]:::p1
        
        P1_Poly --> P1_Proof
        RRData_Class ==>|Instantiates| P1_Proof
        StrongApprox -.->|Provable Instance| P1_Proof
    end

    %% --- Layer 4b: Elliptic Instance (The Current Focus) ---
    subgraph Elliptic_Implementation ["Layer 4b: Genus 1 (Elliptic)"]
        direction TB
        
        %% The Axiom Stack
        Elliptic_Setup["Elliptic/EllipticSetup.lean<br/>(Axiom: IsDedekindDomain)"]:::axiom
        Elliptic_Places["Elliptic/EllipticPlaces.lean<br/>(Local Uniformizers)"]:::elliptic
        Elliptic_Canonical["Elliptic/EllipticCanonical.lean<br/>(Def: K=0, deg=0)"]:::elliptic
        
        %% The H1 Bridge (Cycle 292)
        Elliptic_H1["Elliptic/EllipticH1.lean<br/>(Axioms: H1=1, Vanishing)"]:::axiom
        
        %% The Result (Cycle 293)
        Elliptic_RRData["Elliptic/EllipticRRData.lean<br/>(Result: RR Proved Conditional)"]:::elliptic

        Elliptic_Setup --> Elliptic_Places
        Elliptic_Places --> Elliptic_Canonical
        Elliptic_Canonical --> Elliptic_H1
        
        %% Strong Approx feeds into the Logic
        StrongApprox -.->|Axiom Instance| Elliptic_RRData
        
        Elliptic_H1 --> Elliptic_RRData
        RRData_Class ==>|Instantiates| Elliptic_RRData
    end

    %% --- Global Dependencies ---
    Mathlib((Mathlib)) --> Core_Infrastructure
    Mathlib --> Elliptic_Setup