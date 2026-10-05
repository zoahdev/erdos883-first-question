import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_95 :
    (List.ofFn coreChunks509_95).flatten =
      (coreData509.take (coreResources509 95).q).drop 165 := by
  decide +kernel

theorem coreCheck509_95 :
    ∀ c : Fin 1, (coreChunks509_95 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 95)) = true := by
  decide +kernel
#print axioms coreFlatten509_95
#print axioms coreCheck509_95
end Erdos883Verified
