# UniProt ID Mapping Databases Reference

This document lists the exact database identifiers to use with the `map` command
of `uniprot_tools.py` (i.e. the `--from_db` and `--to_db` arguments).

**Source:** `https://rest.uniprot.org/configure/idmapping/fields`

## Usage

```bash
uv run uniprot_tools.py map "P12345,Q67890" --from_db UniProtKB_AC-ID --to_db PDB
```

--------------------------------------------------------------------------------

## UniProt

-   **UniProtKB**: `UniProtKB` (`--to_db` only)
-   **UniProtKB AC/ID**: `UniProtKB_AC-ID` (`--from_db` only)
-   **UniProtKB/Swiss-Prot**: `UniProtKB-Swiss-Prot` (`--to_db` only)
-   **UniParc**: `UniParc`
-   **UniRef50**: `UniRef50`
-   **UniRef90**: `UniRef90`
-   **UniRef100**: `UniRef100`
-   **Gene Name**: `Gene_Name`
-   **CRC64**: `CRC64`
-   **Proteome ID**: `Proteome_ID` (`--from_db` only)

## Sequence databases

-   **CCDS**: `CCDS`
-   **EMBL/GenBank/DDBJ**: `EMBL-GenBank-DDBJ`
-   **EMBL/GenBank/DDBJ CDS**: `EMBL-GenBank-DDBJ_CDS`
-   **GI number**: `GI_number`
-   **PIR**: `PIR`
-   **RefSeq Nucleotide**: `RefSeq_Nucleotide`
-   **RefSeq Protein**: `RefSeq_Protein`

## 3D structure databases

-   **PDB**: `PDB`

## Protein-protein interaction databases

-   **BioGRID**: `BioGRID`
-   **ComplexPortal**: `ComplexPortal`
-   **DIP**: `DIP`
-   **STRING**: `STRING`

## Chemistry

-   **ChEMBL**: `ChEMBL`
-   **DrugBank**: `DrugBank`
-   **GuidetoPHARMACOLOGY**: `GuidetoPHARMACOLOGY`
-   **SwissLipids**: `SwissLipids`

## Protein family/group databases

-   **Allergome**: `Allergome`
-   **ESTHER**: `ESTHER`
-   **MEROPS**: `MEROPS`
-   **PeroxiBase**: `PeroxiBase`
-   **REBASE**: `REBASE`
-   **TCDB**: `TCDB`

## PTM databases

-   **GlyConnect**: `GlyConnect`

## Genetic variation databases

-   **BioMuta**: `BioMuta`
-   **DMDM**: `DMDM`

## Proteomic databases

-   **CPTAC**: `CPTAC`
-   **ProteomicsDB**: `ProteomicsDB`

## Protocols and materials databases

-   **DNASU**: `DNASU`

## Genome annotation databases

-   **Ensembl**: `Ensembl`
-   **Ensembl Genomes**: `Ensembl_Genomes`
-   **Ensembl Genomes Protein**: `Ensembl_Genomes_Protein`
-   **Ensembl Genomes Transcript**: `Ensembl_Genomes_Transcript`
-   **Ensembl Protein**: `Ensembl_Protein`
-   **Ensembl Transcript**: `Ensembl_Transcript`
-   **GeneID**: `GeneID`
-   **KEGG**: `KEGG`
-   **PATRIC**: `PATRIC`
-   **UCSC**: `UCSC`
-   **WBParaSite**: `WBParaSite`
-   **WBParaSite Transcript/Protein**: `WBParaSite_Transcript-Protein`

## Organism-specific databases

-   **ArachnoServer**: `ArachnoServer`
-   **Araport**: `Araport`
-   **CGD**: `CGD`
-   **ClinPGx**: `ClinPGx`
-   **ConoServer**: `ConoServer`
-   **dictyBase**: `dictyBase`
-   **EchoBASE**: `EchoBASE`
-   **euHCVdb**: `euHCVdb`
-   **FlyBase**: `FlyBase`
-   **GeneCards**: `GeneCards`
-   **GeneReviews**: `GeneReviews`
-   **HGNC**: `HGNC`
-   **LegioList**: `LegioList`
-   **Leproma**: `Leproma`
-   **MaizeGDB**: `MaizeGDB`
-   **MGI**: `MGI`
-   **MIM**: `MIM`
-   **OpenTargets**: `OpenTargets`
-   **Orphanet**: `Orphanet`
-   **PomBase**: `PomBase`
-   **PseudoCAP**: `PseudoCAP`
-   **RGD**: `RGD`
-   **SGD**: `SGD`
-   **TubercuList**: `TubercuList`
-   **VEuPathDB**: `VEuPathDB`
-   **VGNC**: `VGNC`
-   **WormBase**: `WormBase`
-   **WormBase Protein**: `WormBase_Protein`
-   **WormBase Transcript**: `WormBase_Transcript`
-   **Xenbase**: `Xenbase`
-   **ZFIN**: `ZFIN`

## Phylogenomic databases

-   **eggNOG**: `eggNOG`
-   **GeneTree**: `GeneTree`
-   **HOGENOM**: `HOGENOM`
-   **OMA**: `OMA`
-   **OrthoDB**: `OrthoDB`

## Enzyme and pathway databases

-   **BioCyc**: `BioCyc`
-   **PlantReactome**: `PlantReactome`
-   **Reactome**: `Reactome`
-   **UniPathway**: `UniPathway`

## Miscellaneous

-   **ChiTaRS**: `ChiTaRS`
-   **GeneWiki**: `GeneWiki`
-   **GenomeRNAi**: `GenomeRNAi`
-   **PHI-base**: `PHI-base`

## Gene expression databases

-   **CollecTF**: `CollecTF`

## Family and domain databases

-   **DisProt**: `DisProt`
-   **IDEAL**: `IDEAL`

--------------------------------------------------------------------------------

## Mapping Rules (Valid `--to_db` targets per `--from_db` source)

Not all `--from_db` → `--to_db` combinations are valid. The API defines rules
that constrain which target databases are allowed for each source. Some source
databases also require a `taxonId` parameter.

### Rule 1: `UniProtKB_AC-ID` (From only)

When mapping **from** `UniProtKB_AC-ID`, the valid **to** databases are: all
databases listed above (the full set). Default target: `UniProtKB`. Taxon ID:
not required.

### Rule 2: `UniParc`, `Proteome_ID`

When mapping **from** `UniParc` or `Proteome_ID`, the valid **to** databases
are:

-   `UniProtKB`
-   `UniProtKB-Swiss-Prot`
-   `UniParc`

Default target: `UniProtKB`. Taxon ID: not required.

### Rule 3: `UniRef50`

When mapping **from** `UniRef50`, the valid **to** databases are:

-   `UniProtKB`
-   `UniProtKB-Swiss-Prot`
-   `UniRef50`

Default target: `UniProtKB`. Taxon ID: not required.

### Rule 4: `UniRef90`

When mapping **from** `UniRef90`, the valid **to** databases are:

-   `UniProtKB`
-   `UniProtKB-Swiss-Prot`
-   `UniRef90`

Default target: `UniProtKB`. Taxon ID: not required.

### Rule 5: `UniRef100`

When mapping **from** `UniRef100`, the valid **to** databases are:

-   `UniProtKB`
-   `UniProtKB-Swiss-Prot`
-   `UniRef100`

Default target: `UniProtKB`. Taxon ID: not required.

### Rule 6: `Gene_Name`

When mapping **from** `Gene_Name`, the valid **to** databases are:

-   `UniProtKB`
-   `UniProtKB-Swiss-Prot`

Default target: `UniProtKB`. **Taxon ID: required** (use `&taxId=XXXXX`).

### Rule 7: All other databases (default rule)

When mapping **from** any other database (CCDS, EMBL-GenBank-DDBJ, PDB, GeneID,
Ensembl, HGNC, etc.), the valid **to** databases are:

-   `UniProtKB`
-   `UniProtKB-Swiss-Prot`

Default target: `UniProtKB`. Taxon ID: not required.

--------------------------------------------------------------------------------

## Quick Reference: From-only and To-only databases

### From-only databases (cannot be used as `--to_db`)

-   **UniProtKB AC/ID**: `UniProtKB_AC-ID`
-   **Proteome ID**: `Proteome_ID`

### To-only databases (cannot be used as `--from_db`)

-   **UniProtKB**: `UniProtKB`
-   **UniProtKB/Swiss-Prot**: `UniProtKB-Swiss-Prot`

### Common mapping examples

```bash
# Map UniProt accessions to PDB IDs
uv run uniprot_tools.py map "P12345" --from_db UniProtKB_AC-ID --to_db PDB

# Map PDB IDs to UniProt accessions
uv run uniprot_tools.py map "1AKE" --from_db PDB --to_db UniProtKB

# Map gene names to UniProt (requires taxon ID in the API, handled internally)
uv run uniprot_tools.py map "BRCA1" --from_db Gene_Name --to_db UniProtKB

# Map RefSeq protein IDs to UniProtKB/Swiss-Prot (reviewed entries only)
uv run uniprot_tools.py map "NP_005219.2" --from_db RefSeq_Protein --to_db UniProtKB-Swiss-Prot

# Map Ensembl gene IDs to UniProtKB
uv run uniprot_tools.py map "ENSG00000141510" --from_db Ensembl --to_db UniProtKB

# Map EMBL/GenBank accessions to UniProtKB
uv run uniprot_tools.py map "M10051" --from_db EMBL-GenBank-DDBJ --to_db UniProtKB

# Map HGNC IDs to UniProtKB
uv run uniprot_tools.py map "HGNC:11998" --from_db HGNC --to_db UniProtKB
```
