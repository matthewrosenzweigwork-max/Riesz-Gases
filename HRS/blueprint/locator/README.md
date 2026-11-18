# Build the supplemental paper locator

From a Python 3 environment with lxml, where HRS contains the full source and the shipped proof supplement:

```sh
D=/path/to/HRS
python3 "$D/blueprint/locator/coverage.py" \
  --tree "$D" --inventory "$D/blueprint/locator/inventory" \
  --titles "$D/blueprint/locator/titles.json" \
  --providers "$D/blueprint/locator/providers.json" --output /new/output/coverage
```

The output directory must be new. The manuscript heading/locator tables in `HRS/coverage/` are build inputs. The exact type-check source for the 347 base terms and for the two restored terms is included. The index checks all referenced source bytes when generating numbered Lean pages. It reports the named declaration separately from its proved formulation. A paper locus is not a verification of the written argument.
