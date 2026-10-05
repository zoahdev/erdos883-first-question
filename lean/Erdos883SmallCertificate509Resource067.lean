import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_67 :
    (List.ofFn coreChunks509_67).flatten =
      (coreData509.take (coreResources509 67).q).drop 124 := by
  decide +kernel

theorem coreCheck509_67 :
    ∀ c : Fin 1, (coreChunks509_67 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 67)) = true := by
  decide +kernel
#print axioms coreFlatten509_67
#print axioms coreCheck509_67
end Erdos883Verified
