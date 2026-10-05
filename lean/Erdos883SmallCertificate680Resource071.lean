import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_71 :
    (List.ofFn coreChunks680_71).flatten =
      (coreData680.take (coreResources680 71).q).drop 135 := by
  decide +kernel

theorem coreCheck680_71 :
    ∀ c : Fin 1, (coreChunks680_71 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 71)) = true := by
  decide +kernel
#print axioms coreFlatten680_71
#print axioms coreCheck680_71
end Erdos883Verified
