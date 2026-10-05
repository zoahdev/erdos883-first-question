import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_71 :
    (List.ofFn coreChunks509_71).flatten =
      (coreData509.take (coreResources509 71).q).drop 132 := by
  decide +kernel

theorem coreCheck509_71 :
    ∀ c : Fin 1, (coreChunks509_71 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 71)) = true := by
  decide +kernel
#print axioms coreFlatten509_71
#print axioms coreCheck509_71
end Erdos883Verified
