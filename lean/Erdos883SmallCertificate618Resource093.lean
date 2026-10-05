import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_93 :
    (List.ofFn coreChunks618_93).flatten =
      (coreData618.take (coreResources618 93).q).drop 195 := by
  decide +kernel

theorem coreCheck618_93 :
    ∀ c : Fin 1, (coreChunks618_93 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 93)) = true := by
  decide +kernel
#print axioms coreFlatten618_93
#print axioms coreCheck618_93
end Erdos883Verified
