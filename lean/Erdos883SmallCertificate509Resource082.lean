import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_82 :
    (List.ofFn coreChunks509_82).flatten =
      (coreData509.take (coreResources509 82).q).drop 161 := by
  decide +kernel

theorem coreCheck509_82 :
    ∀ c : Fin 1, (coreChunks509_82 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 82)) = true := by
  decide +kernel
#print axioms coreFlatten509_82
#print axioms coreCheck509_82
end Erdos883Verified
