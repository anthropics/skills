# ClinicalTrials.gov Study Data Schema

This reference documents the JSON structure and field paths returned by the
ClinicalTrials.gov API v2. Use these paths with the `--fields` parameter to
select specific data.

## Top-Level Response

**Multi-study query** (`/studies`):

- `totalCount` — integer (present when countTotal=true)
- `studies[]` — array of study objects
- `nextPageToken` — string (omitted on final page)

**Single-study query** (`/studies/{nctId}`): returns a study object directly.

## Study Object Structure

Each study has two major sections: `protocolSection` and `resultsSection`, plus
a `hasResults` boolean.

### Protocol Section

#### Identification Module

- `protocolSection.identificationModule.nctId` (`NCTId`)
  — Unique trial identifier
- `protocolSection.identificationModule.briefTitle` (`BriefTitle`)
  — Short public title
- `protocolSection.identificationModule.officialTitle` (`OfficialTitle`)
  — Full scientific title
- `protocolSection.identificationModule.organization.fullName` (`Organization`)
  — Sponsoring organization

#### Status Module

- `protocolSection.statusModule.overallStatus` (`OverallStatus`)
  — Recruitment status. Values: RECRUITING, NOT_YET_RECRUITING,
  ACTIVE_NOT_RECRUITING, ENROLLING_BY_INVITATION, COMPLETED, SUSPENDED,
  TERMINATED, WITHDRAWN
- `protocolSection.statusModule.startDateStruct.date` (`StartDate`)
  — Study start date
- `protocolSection.statusModule.primaryCompletionDateStruct.date`
  (`PrimaryCompletionDate`) — Primary outcome completion
- `protocolSection.statusModule.completionDateStruct.date` (`CompletionDate`)
  — Full study completion
- `protocolSection.statusModule.lastUpdatePostDateStruct.date`
  (`LastUpdatePostDate`) — Last record update

#### Sponsor/Collaborators Module

- `protocolSection.sponsorCollaboratorsModule.leadSponsor.name`
  (`LeadSponsorName`) — Lead sponsor

#### Description Module

- `protocolSection.descriptionModule.briefSummary` (`BriefSummary`)
  — Short study description
- `protocolSection.descriptionModule.detailedDescription`
  (`DetailedDescription`) — Extended scientific description

#### Conditions Module

- `protocolSection.conditionsModule.conditions` (`ConditionsModule`)
  — Conditions module (includes array of diseases)
- `protocolSection.conditionsModule.keywords` (`Keywords`)
  — Categorization terms

#### Design Module

- `protocolSection.designModule.studyType` (`StudyType`)
  — INTERVENTIONAL, OBSERVATIONAL, or EXPANDED_ACCESS
- `protocolSection.designModule.phases` (`Phase`)
  — Array: EARLY_PHASE1, PHASE1, PHASE2, PHASE3, PHASE4, NA
- `protocolSection.designModule.enrollmentInfo.count` (`EnrollmentCount`)
  — Participant count (actual or estimated)

#### Arms & Interventions Module

- `protocolSection.armsInterventionsModule.armGroups` (`ArmGroup`)
  — Trial arms with labels and descriptions
- `protocolSection.armsInterventionsModule.interventions`
  (`ArmsInterventionsModule`) — Arms and treatments (DRUG, DEVICE, etc.)

#### Outcomes Module

- `protocolSection.outcomesModule.primaryOutcomes` (`PrimaryOutcome`)
  — Primary endpoints
- `protocolSection.outcomesModule.secondaryOutcomes` (`SecondaryOutcome`)
  — Secondary endpoints

#### Eligibility Module

- `protocolSection.eligibilityModule.eligibilityCriteria`
  (`EligibilityCriteria`) — Full inclusion/exclusion text
- `protocolSection.eligibilityModule.sex` (`Sex`) — ALL, MALE, or FEMALE
- `protocolSection.eligibilityModule.minimumAge` (`MinimumAge`)
  — e.g. "18 Years"
- `protocolSection.eligibilityModule.maximumAge` (`MaximumAge`)
  — e.g. "65 Years"
- `protocolSection.eligibilityModule.healthyVolunteers` (`HealthyVolunteers`)
  — Boolean
- `protocolSection.eligibilityModule.stdAges` (`StdAge`)
  — Array: CHILD, ADULT, OLDER_ADULT

To retrieve just the eligibility module, use:
`--fields "NCTId,BriefTitle,EligibilityModule"` or the
`get-eligibility` command.

#### Contacts & Locations Module

- `protocolSection.contactsLocationsModule.centralContacts` (`CentralContact`) —
  Primary contact persons
- `protocolSection.contactsLocationsModule.locations` (`LocationFacility`) —
  Facilities with city, state, country, and status

### Results Section

Available when `hasResults` is `true`.

- **Participant Flow Module** — Participant counts per study period
- **Baseline Characteristics Module** — Demographics and baseline data
- **Outcome Measures Module** — Statistical results for primary/secondary
  outcomes
- **Adverse Events Module** — Serious and other adverse event data

## Common `--fields` Recipes

- **Overview:**
  `NCTId,BriefTitle,OverallStatus,Phase,ConditionsModule`
- **Eligibility details:**
  `NCTId,BriefTitle,EligibilityModule`
- **Interventions:**
  `NCTId,BriefTitle,ArmsInterventionsModule`
- **Locations:**
  `NCTId,ContactsLocationsModule`
- **Outcomes:**
  `NCTId,PrimaryOutcome,SecondaryOutcome`
- **Sponsor info:**
  `NCTId,BriefTitle,LeadSponsorName,Organization`
- **Full protocol summary:**
  `NCTId,BriefTitle,OverallStatus,Phase,BriefSummary,ConditionsModule,`
  `ArmsInterventionsModule,EligibilityModule`
