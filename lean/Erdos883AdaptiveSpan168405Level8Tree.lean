import Erdos883AdaptiveSpan168405Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength168405_8 : adaptiveNumericSpans168405_8.length = 746 := by decide +kernel
theorem adaptiveSpanEvenCache168405_8 : adaptiveSpanEven168405_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain168405_8 : adaptiveSpanEven168405_8.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanEvenEntries168405_8 : adaptiveSpanEven168405_8.spans = coreEvenSpans 84203 0 adaptiveNumericSpans168405_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache168405_8 : adaptiveSpanWhole168405_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain168405_8 : adaptiveSpanWhole168405_8.domainCheck 84203 = true := by decide +kernel
theorem adaptiveSpanWholeEntries168405_8 : adaptiveSpanWhole168405_8.spans = coreWholeSpans 0 adaptiveNumericSpans168405_8 := by
  decide +kernel
end Erdos883Verified
