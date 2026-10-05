import Erdos883AdaptiveSpan64924Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength64924_2 : adaptiveNumericSpans64924_2.length = 567 := by decide +kernel
theorem adaptiveSpanEvenCache64924_2 : adaptiveSpanEven64924_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain64924_2 : adaptiveSpanEven64924_2.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanEvenEntries64924_2 : adaptiveSpanEven64924_2.spans = coreEvenSpans 32462 0 adaptiveNumericSpans64924_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache64924_2 : adaptiveSpanWhole64924_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain64924_2 : adaptiveSpanWhole64924_2.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanWholeEntries64924_2 : adaptiveSpanWhole64924_2.spans = coreWholeSpans 0 adaptiveNumericSpans64924_2 := by
  decide +kernel
end Erdos883Verified
