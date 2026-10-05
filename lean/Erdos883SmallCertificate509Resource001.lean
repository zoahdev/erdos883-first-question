import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_1 :
    (List.ofFn coreChunks509_1).flatten =
      (coreData509.take (coreResources509 1).q).drop 48 := by
  decide +kernel

theorem coreCheck509_1 :
    ∀ c : Fin 1, (coreChunks509_1 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 1)) = true := by
  decide +kernel
#print axioms coreFlatten509_1
#print axioms coreCheck509_1
end Erdos883Verified
