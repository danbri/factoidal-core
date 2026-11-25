# Report missing image response bodies in offline captures

The captured UK BBC homepage recorded HTTP 200 for its first-row photos without their bodies. Replay returned empty successful images, so checking URL misses did not detect them. Omit these incomplete image responses and record them as skipped. If another captured request for the same URL contains bytes, that response can still be saved.
