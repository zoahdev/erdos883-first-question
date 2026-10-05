import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_121 :
    (List.ofFn coreChunks680_121).flatten =
      (coreData680.take (coreResources680 121).q).drop 288 := by
  decide +kernel

theorem coreCheck680_121 :
    ∀ c : Fin 1, (coreChunks680_121 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 121)) = true := by
  decide +kernel
#print axioms coreFlatten680_121
#print axioms coreCheck680_121
end Erdos883Verified
