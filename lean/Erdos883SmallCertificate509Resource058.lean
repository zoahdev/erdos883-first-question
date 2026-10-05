import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_58 :
    (List.ofFn coreChunks509_58).flatten =
      (coreData509.take (coreResources509 58).q).drop 108 := by
  decide +kernel

theorem coreCheck509_58 :
    ∀ c : Fin 1, (coreChunks509_58 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 58)) = true := by
  decide +kernel
#print axioms coreFlatten509_58
#print axioms coreCheck509_58
end Erdos883Verified
