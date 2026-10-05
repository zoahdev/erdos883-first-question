import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_18 :
    (List.ofFn coreChunks509_18).flatten =
      (coreData509.take (coreResources509 18).q).drop 108 := by
  decide +kernel

theorem coreCheck509_18 :
    ∀ c : Fin 1, (coreChunks509_18 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 18)) = true := by
  decide +kernel
#print axioms coreFlatten509_18
#print axioms coreCheck509_18
end Erdos883Verified
