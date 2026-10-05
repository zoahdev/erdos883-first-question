import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_12 :
    (List.ofFn coreChunks509_12).flatten =
      (coreData509.take (coreResources509 12).q).drop 101 := by
  decide +kernel

theorem coreCheck509_12 :
    ∀ c : Fin 1, (coreChunks509_12 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 12)) = true := by
  decide +kernel
#print axioms coreFlatten509_12
#print axioms coreCheck509_12
end Erdos883Verified
