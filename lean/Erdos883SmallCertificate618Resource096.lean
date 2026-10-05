import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_96 :
    (List.ofFn coreChunks618_96).flatten =
      (coreData618.take (coreResources618 96).q).drop 220 := by
  decide +kernel

theorem coreCheck618_96 :
    ∀ c : Fin 1, (coreChunks618_96 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 96)) = true := by
  decide +kernel
#print axioms coreFlatten618_96
#print axioms coreCheck618_96
end Erdos883Verified
