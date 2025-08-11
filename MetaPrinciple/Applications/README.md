# Applications Directory

**WARNING**: This directory contains phenomenological applications and empirical predictions.

## Do Not Use These In Core Proofs

Files in this directory:
- Depend on calibrations to SI units
- Make additional physical assumptions beyond the core ledger
- Contain model-dependent predictions

## Contents

- `FineStructure.lean` - Fine structure constant (requires voxel Regge model)
- `MuonG2.lean` - Muon anomalous magnetic moment (requires breath cycle model)
- `DarkMatter.lean` - Dark matter fraction (requires cosmological calibration)
- `ILGKernel.lean` - Modified gravity kernel (emergent phenomenology)

## For AI Agents

**DO NOT** import these modules into Core/ or Interfaces/ directories.
These are applications that test the framework, not part of the logical foundation.
