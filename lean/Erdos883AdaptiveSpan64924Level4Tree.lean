import Erdos883AdaptiveSpan64924Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength64924_4 : adaptiveNumericSpans64924_4.length = 567 := by decide +kernel
theorem adaptiveSpanEvenCache64924_4 : adaptiveSpanEven64924_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain64924_4 : adaptiveSpanEven64924_4.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanEvenEntries64924_4 : adaptiveSpanEven64924_4.spans = coreEvenSpans 32462 0 adaptiveNumericSpans64924_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache64924_4 : adaptiveSpanWhole64924_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain64924_4 : adaptiveSpanWhole64924_4.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanWholeEntries64924_4 : adaptiveSpanWhole64924_4.spans = coreWholeSpans 0 adaptiveNumericSpans64924_4 := by
  decide +kernel
end Erdos883Verified
