
import asyncio
import traceback

from aardwolf.protocol.T124.userdata.constants import ChannelOption

class Channel:
	def __init__(self, name:str, options:ChannelOption = ChannelOption.INITIALIZED|ChannelOption.ENCRYPT_RDP):
		self.name = name
		self.options = options
		self.channel_id = None
		self.connection = None

	def get_name(self):
		return self.name
	
	async def disconnect(self):
		try:
			_, err = await self.stop()
			if err is not None:
				raise err
		except:
			pass

	async def run(self, connection):
		try:
			self.connection = connection
			_, err = await self.start()
			if err is not None:
				raise err
			return True, None
		except Exception as e:
			traceback.print_exc()
			return None, e


	async def start(self):
		# Override this when implementing new channel type
		try:
			return True, None
		except Exception as e:
			return None, e
	
	async def stop(self):
		# Override this when implementing new channel type
		try:
			return True, None
		except Exception as e:
			return None, e

	async def process_channel_data(self, data):
		# This function will be called when channel data is recieved from the server
		raise NotImplementedError()
	
	async def process_user_data(self, data):
		# This function will be called when the channel recieves a new user data
		# Override this function to implement user data processing
		raise NotImplementedError()
	
	async def send_channel_data(self, dataobj, sec_hdr, datacontrol_hdr, sharecontrol_hdr, is_fastpath):
		await self.connection.handle_out_data(dataobj, sec_hdr, datacontrol_hdr, sharecontrol_hdr, self.channel_id, is_fastpath)

	async def send_user_data(self, msg):
		await self.connection.ext_out_queue.put(msg)


class MCSChannel(Channel):
	name = 'MCS'
	def __init__(self, iosettings = None):
		Channel.__init__(self, self.name, ChannelOption.INITIALIZED|ChannelOption.ENCRYPT_RDP)
		self.out_queue = asyncio.Queue()
	

	async def process_channel_data(self, data):
		# This function will be called when channel data is recieved from the server
		print(f'📬 MCSChannel.process_channel_data: Received {len(data) if data else 0} bytes, putting in out_queue')
		print(f'   Queue size before put: {self.out_queue.qsize()}')
		await self.out_queue.put((data, None))
		print(f'   Queue size after put: {self.out_queue.qsize()}')