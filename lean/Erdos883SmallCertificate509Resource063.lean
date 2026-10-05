import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_63 :
    (List.ofFn coreChunks509_63).flatten =
      (coreData509.take (coreResources509 63).q).drop 115 := by
  decide +kernel

theorem coreCheck509_63 :
    ∀ c : Fin 1, (coreChunks509_63 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 63)) = true := by
  decide +kernel
#print axioms coreFlatten509_63
#print axioms coreCheck509_63
end Erdos883Verified
