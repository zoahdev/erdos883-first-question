import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_39 :
    (List.ofFn coreChunks509_39).flatten =
      (coreData509.take (coreResources509 39).q).drop 83 := by
  decide +kernel

theorem coreCheck509_39 :
    ∀ c : Fin 1, (coreChunks509_39 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 39)) = true := by
  decide +kernel
#print axioms coreFlatten509_39
#print axioms coreCheck509_39
end Erdos883Verified
