import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_90 :
    (List.ofFn coreChunks509_90).flatten =
      (coreData509.take (coreResources509 90).q).drop 218 := by
  decide +kernel

theorem coreCheck509_90 :
    ∀ c : Fin 1, (coreChunks509_90 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 90)) = true := by
  decide +kernel
#print axioms coreFlatten509_90
#print axioms coreCheck509_90
end Erdos883Verified
