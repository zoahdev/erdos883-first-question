import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_27 :
    (List.ofFn coreChunks509_27).flatten =
      (coreData509.take (coreResources509 27).q).drop 119 := by
  decide +kernel

theorem coreCheck509_27 :
    ∀ c : Fin 1, (coreChunks509_27 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 27)) = true := by
  decide +kernel
#print axioms coreFlatten509_27
#print axioms coreCheck509_27
end Erdos883Verified
