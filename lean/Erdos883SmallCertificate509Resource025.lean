import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_25 :
    (List.ofFn coreChunks509_25).flatten =
      (coreData509.take (coreResources509 25).q).drop 115 := by
  decide +kernel

theorem coreCheck509_25 :
    ∀ c : Fin 1, (coreChunks509_25 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 25)) = true := by
  decide +kernel
#print axioms coreFlatten509_25
#print axioms coreCheck509_25
end Erdos883Verified
