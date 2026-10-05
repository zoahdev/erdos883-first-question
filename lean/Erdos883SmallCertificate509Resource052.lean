import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_52 :
    (List.ofFn coreChunks509_52).flatten =
      (coreData509.take (coreResources509 52).q).drop 100 := by
  decide +kernel

theorem coreCheck509_52 :
    ∀ c : Fin 1, (coreChunks509_52 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 52)) = true := by
  decide +kernel
#print axioms coreFlatten509_52
#print axioms coreCheck509_52
end Erdos883Verified
